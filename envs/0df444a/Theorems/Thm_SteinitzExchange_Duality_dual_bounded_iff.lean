-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_dual_bounded_iff
-- name    : SteinitzExchange.Duality.dual_bounded_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:58:57.494672+00:00
-- url     : https://prove2.me/theorems/950befe6-a25f-4f1f-8ee7-350e530aa1d7
-- title:
--   Lemma 6.7 — four equivalent forms of boundedness of the dual problem
-- statement:
--   Let $B_1,B_2\subseteq\mathbb Z^V$ be finite integral base sets and $\omega:B_1\to\mathbb R$, $\zeta:B_2\to\mathbb R$ arbitrary functions. Let $g_1(X)=\min\{x(X)\mid x\in B_1\}$ be the supermodular function describing $B_1$, $f_2(X)=\max\{x(X)\mid x\in B_2\}$ the submodular function describing $B_2$, and
--
--   $$\psi_1^\circ(p)=\min\{\langle p,x\rangle\mid x\in B_1\},\qquad \psi_2^\bullet(p)=\max\{\langle p,x\rangle\mid x\in B_2\}.$$
--
--   Then the following four conditions are equivalent:
--
--   1. (6.7) $\inf\{\zeta^\bullet(p)-\omega^\circ(p)\mid p\in\mathbb Z^V\}\neq-\infty$;
--   2. (6.8) $\inf\{\zeta^\bullet(p)-\omega^\circ(p)\mid p\in\mathbb R^V\}\neq-\infty$;
--   3. (6.9) $\psi_2^\bullet(p)\ge\psi_1^\circ(p)$ for all $p\in\mathbb R^V$;
--   4. (6.10) $f_2(X)\ge g_1(X)$ for all $X\subseteq V$, and $f_2(V)=g_1(V)$.
--
--   Together with Frank's discrete separation theorem, this gives part (P1) of the duality theorem.
--
--   **Formalization Note.** The two infima are `dualValueInt` and `dualValue` in `EReal`; "$\neq-\infty$" is `≠ ⊥`, i.e. boundedness below. The four-way equivalence is stated as the chain (6.7)⇔(6.8), (6.8)⇔(6.9), (6.9)⇔(6.10).
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 297, Lemma 6.7 (Eqs. (6.7)-(6.10))

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Conjugate
import Definitions.Def_SteinitzExchange_Duality_SetFunction
import Definitions.Def_SteinitzExchange_Duality_Problems

namespace SteinitzExchange.Duality

/-- Murota 1996, p. 297, Lemma 6.7. Let `B₁, B₂ ⊆ ℤ^V` be finite integral base sets,
`ω : B₁ → ℝ`, `ζ : B₂ → ℝ` arbitrary, `g₁(X) = min{x(X) | x ∈ B₁}`,
`f₂(X) = max{x(X) | x ∈ B₂}`, `ψ₁°(p) = min{⟨p, x⟩ | x ∈ B₁}`, `ψ₂•(p) = max{⟨p, x⟩ | x ∈ B₂}`.
The following are equivalent:
(6.7) `inf{ζ•(p) − ω°(p) | p ∈ ℤ^V} ≠ −∞`;
(6.8) `inf{ζ•(p) − ω°(p) | p ∈ ℝ^V} ≠ −∞`;
(6.9) `ψ₂•(p) ≥ ψ₁°(p)` for all `p ∈ ℝ^V`;
(6.10) `f₂(X) ≥ g₁(X)` for all `X ⊆ V`, and `f₂(V) = g₁(V)`. -/
theorem dual_bounded_iff {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B₁ B₂ : Finset (V → ℤ)) (hB₁ : IsIntegralBaseSet B₁) (hB₂ : IsIntegralBaseSet B₂)
    (ω ζ : (V → ℤ) → ℝ) :
    (dualValueInt B₁ B₂ ω ζ ≠ ⊥ ↔ dualValue B₁ B₂ ω ζ ≠ ⊥) ∧
    (dualValue B₁ B₂ ω ζ ≠ ⊥ ↔ ∀ p : V → ℝ, supportMin B₁ p ≤ supportMax B₂ p) ∧
    ((∀ p : V → ℝ, supportMin B₁ p ≤ supportMax B₂ p) ↔
      (∀ X : Finset V, setMin B₁ X ≤ setMax B₂ X) ∧
        setMax B₂ Finset.univ = setMin B₁ Finset.univ) := by sorry

end SteinitzExchange.Duality
