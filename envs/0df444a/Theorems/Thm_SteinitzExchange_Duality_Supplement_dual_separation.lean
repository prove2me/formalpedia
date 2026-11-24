-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_Supplement_dual_separation
-- name    : SteinitzExchange.Duality.Supplement.dual_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:28:30.278646+00:00
-- url     : https://prove2.me/theorems/7001b646-34a3-4ad0-b187-c9a0c0a6020a
-- title:
--   Theorem 6.9 — dual separation theorem for M-concave/M-convex pairs, with a common integer base and integral intercept
-- statement:
--   Let $V$ be a finite nonempty set and $B_1,B_2\subseteq\mathbb Z^V$ finite integral base sets (finite nonempty sets satisfying the exchange axiom (B1)). For $\omega:B_1\to\mathbb R$ let $\omega^\circ(p)=\min\{\langle p,x\rangle-\omega(x)\mid x\in B_1\}$ be its concave conjugate, and for $\zeta:B_2\to\mathbb R$ let $\zeta^\bullet(p)=\max\{\langle p,x\rangle-\zeta(x)\mid x\in B_2\}$ be its convex conjugate ($p\in\mathbb R^V$).
--
--   Suppose that $\omega$ and $-\zeta$ satisfy the exchange property (EXC), and that
--   $$\omega^\circ(p)\le\zeta^\bullet(p)\qquad(p\in\mathbb R^V).$$
--   Then there exist $\beta^*\in\mathbb R$ and a common base $x^*\in B_1\cap B_2$ such that
--   $$\omega^\circ(p)\le\beta^*+\langle p,x^*\rangle\le\zeta^\bullet(p)\qquad(p\in\mathbb R^V).\tag{6.15}$$
--   Moreover, if $\omega$ and $\zeta$ are integer-valued (on $B_1$ and $B_2$ respectively), there exist such $\beta^*\in\mathbb Z$ and $x^*\in B_1\cap B_2$.
--
--   This is the separation theorem for the conjugate pair $(\omega^\circ,\zeta^\bullet)$, dual to the primal separation theorem (Theorem 6.8); in particular the hypothesis forces $B_1\cap B_2\neq\emptyset$.
--
--   **Formalization Note.** The conjugates are the published `concaveConj B₁ ω` and `convexConj B₂ ζ`; `pairing p (toReal x)` is $\langle p,x\rangle$. Integer-valuedness is stated only on each function's own domain.
--
--   Differences from the source: none.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 300, Theorem 6.9 (Eq. (6.15))

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Exchange
import Definitions.Def_SteinitzExchange_Duality_Conjugate

namespace SteinitzExchange.Duality.Supplement

/-- Murota 1996, p. 300, Theorem 6.9 (Dual Separation Theorem). Let `B₁, B₂ ⊆ ℤ^V` be finite
integral base sets and `ω : B₁ → ℝ`, `ζ : B₂ → ℝ` such that `ω` and `−ζ` satisfy (EXC). If
`ω°(p) ≤ ζ•(p)` for all `p ∈ ℝ^V`, there exist `β* ∈ ℝ` and `x* ∈ B₁ ∩ B₂` with
`ω°(p) ≤ β* + ⟨p, x*⟩ ≤ ζ•(p)` for all `p ∈ ℝ^V`. Moreover, if `ω` and `ζ` are integer-valued,
there exists such a `β*` in `ℤ`. -/
theorem dual_separation {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B₁ B₂ : Finset (V → ℤ)) (hB₁ : IsIntegralBaseSet B₁) (hB₂ : IsIntegralBaseSet B₂)
    (ω ζ : (V → ℤ) → ℝ) (hω : SatisfiesEXC B₁ ω) (hζ : SatisfiesEXC B₂ (fun x => -ζ x))
    (hle : ∀ p : V → ℝ, concaveConj B₁ ω p ≤ convexConj B₂ ζ p) :
    (∃ β : ℝ, ∃ xs ∈ B₁ ∩ B₂, ∀ p : V → ℝ,
      concaveConj B₁ ω p ≤ β + pairing p (toReal xs) ∧
        β + pairing p (toReal xs) ≤ convexConj B₂ ζ p) ∧
    ((∀ x ∈ B₁, ∃ k : ℤ, ω x = k) → (∀ x ∈ B₂, ∃ k : ℤ, ζ x = k) →
      ∃ β : ℤ, ∃ xs ∈ B₁ ∩ B₂, ∀ p : V → ℝ,
        concaveConj B₁ ω p ≤ (β : ℝ) + pairing p (toReal xs) ∧
          (β : ℝ) + pairing p (toReal xs) ≤ convexConj B₂ ζ p) := by sorry

end SteinitzExchange.Duality.Supplement
