-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_fenchel_min_max
-- name    : SteinitzExchange.Duality.fenchel_min_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:59:50.523846+00:00
-- url     : https://prove2.me/theorems/b77b388e-012b-4c6b-b770-08c37f44fc24
-- title:
--   Theorem 6.4 — Fenchel-type min-max duality with primal and dual integrality for M-concave $\omega$ and M-convex $\zeta$
-- statement:
--   Let $B_1,B_2\subseteq\mathbb Z^V$ be finite integral base sets and let $\omega:B_1\to\mathbb R$ and $\zeta:B_2\to\mathbb R$ be such that $\omega$ and $-\zeta$ satisfy (EXC). Take $\omega^\circ,\hat\omega$ with respect to $B_1$ and $\zeta^\bullet,\check\zeta$ with respect to $B_2$.
--
--   1. **Primal integrality.** $$\max\{\omega(x)-\zeta(x)\mid x\in B_1\cap B_2\}=\max\{\hat\omega(b)-\check\zeta(b)\mid b\in\overline{B_1}\cap\overline{B_2}\}=\inf\{\zeta^\bullet(p)-\omega^\circ(p)\mid p\in\mathbb R^V\}.$$ More precisely:
--      - (P1) if $\inf\{\zeta^\bullet(p)-\omega^\circ(p)\mid p\in\mathbb R^V\}\neq-\infty$, then $B_1\cap B_2\neq\emptyset$;
--      - (P2) if $B_1\cap B_2\neq\emptyset$, all these values are finite and equal, and the infimum is attained by some $p\in\mathbb R^V$.
--   2. **Dual integrality.** If $\omega$ and $\zeta$ are integer-valued, the infimum can be taken over integral vectors: $$\max\{\omega(x)-\zeta(x)\mid x\in B_1\cap B_2\}=\inf\{\zeta^\bullet(p)-\omega^\circ(p)\mid p\in\mathbb Z^V\},$$ and the infimum is attained by some $p\in\mathbb Z^V$ if it is finite.
--
--   A maximum over an empty family is $-\infty$. According to the paper, the formula unifies Edmonds' polymatroid intersection theorem, Fujishige's Fenchel-type duality theorem and Frank's discrete separation theorem with Iri–Tomizawa's potential characterization for the independent assignment problem and its extensions by Fujishige and Frank (weight splitting).
--
--   **Formalization Note.** The three values are `EReal` (`primalValue`, `relaxedValue`, `dualValue`, and `dualValueInt` over $\mathbb Z^V$), with `⊥` the paper's $-\infty$ and the supremum of the empty family equal to `⊥`. (P2) is stated as the existence of $x\in B_1\cap B_2$, $b\in\overline{B_1}\cap\overline{B_2}$ and $p\in\mathbb R^V$ at which the three values are attained, as equal real numbers ("max" includes attainment of both maxima). M-convexity of $\zeta$ is (EXC) for $-\zeta$. Integer-valued means $\omega(x)\in\mathbb Z$ for $x\in B_1$ and $\zeta(x)\in\mathbb Z$ for $x\in B_2$; "finite" for the integral infimum is `≠ ⊥`.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 295, Theorem 6.4

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Exchange
import Definitions.Def_SteinitzExchange_Duality_Conjugate
import Definitions.Def_SteinitzExchange_Duality_Problems

namespace SteinitzExchange.Duality

/-- Murota 1996, p. 295, Theorem 6.4 (Fenchel-type min-max duality). Let `B₁, B₂ ⊆ ℤ^V` be finite
integral base sets and `ω : B₁ → ℝ`, `ζ : B₂ → ℝ` such that `ω` and `−ζ` satisfy (EXC).
(1) [Primal integrality]
`max{ω(x) − ζ(x) | x ∈ B₁ ∩ B₂} = max{ω̂(b) − ζ̌(b) | b ∈ B̄₁ ∩ B̄₂} = inf{ζ•(p) − ω°(p) | p ∈ ℝ^V}`
(in `EReal`, `max ∅ = −∞`); more precisely
(P1) if the infimum is `≠ −∞` then `B₁ ∩ B₂ ≠ ∅`;
(P2) if `B₁ ∩ B₂ ≠ ∅`, all three values are finite and equal, both maxima are attained, and the
infimum is attained by some `p ∈ ℝ^V`.
(2) [Dual integrality] If `ω` and `ζ` are integer-valued, the infimum may be taken over `ℤ^V`:
`max{ω(x) − ζ(x) | x ∈ B₁ ∩ B₂} = inf{ζ•(p) − ω°(p) | p ∈ ℤ^V}`, and it is attained by some
`p ∈ ℤ^V` if it is finite. -/
theorem fenchel_min_max {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B₁ B₂ : Finset (V → ℤ)) (hB₁ : IsIntegralBaseSet B₁) (hB₂ : IsIntegralBaseSet B₂)
    (ω ζ : (V → ℤ) → ℝ) (hω : SatisfiesEXC B₁ ω) (hζ : SatisfiesEXC B₂ (fun x => -ζ x)) :
    -- (1)
    (primalValue B₁ B₂ ω ζ = relaxedValue B₁ B₂ ω ζ ∧
      relaxedValue B₁ B₂ ω ζ = dualValue B₁ B₂ ω ζ) ∧
    -- (P1)
    (dualValue B₁ B₂ ω ζ ≠ ⊥ → (B₁ ∩ B₂).Nonempty) ∧
    -- (P2)
    ((B₁ ∩ B₂).Nonempty →
      ∃ x ∈ B₁ ∩ B₂, ∃ b ∈ hull B₁ ∩ hull B₂, ∃ p : V → ℝ,
        primalValue B₁ B₂ ω ζ = ((ω x - ζ x : ℝ) : EReal) ∧
        relaxedValue B₁ B₂ ω ζ =
          ((concaveClosure B₁ ω b - convexClosure B₂ ζ b : ℝ) : EReal) ∧
        dualValue B₁ B₂ ω ζ = ((convexConj B₂ ζ p - concaveConj B₁ ω p : ℝ) : EReal) ∧
        ω x - ζ x = concaveClosure B₁ ω b - convexClosure B₂ ζ b ∧
        ω x - ζ x = convexConj B₂ ζ p - concaveConj B₁ ω p) ∧
    -- (2)
    ((∀ x ∈ B₁, ∃ k : ℤ, ω x = k) → (∀ x ∈ B₂, ∃ k : ℤ, ζ x = k) →
      primalValue B₁ B₂ ω ζ = dualValueInt B₁ B₂ ω ζ ∧
      (dualValueInt B₁ B₂ ω ζ ≠ ⊥ →
        ∃ p : V → ℤ, dualValueInt B₁ B₂ ω ζ =
          ((convexConj B₂ ζ (toReal p) - concaveConj B₁ ω (toReal p) : ℝ) : EReal))) := by sorry

end SteinitzExchange.Duality
