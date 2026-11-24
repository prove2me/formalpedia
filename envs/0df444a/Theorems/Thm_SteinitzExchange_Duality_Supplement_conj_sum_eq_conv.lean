-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_Supplement_conj_sum_eq_conv
-- name    : SteinitzExchange.Duality.Supplement.conj_sum_eq_conv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:29:47.590994+00:00
-- url     : https://prove2.me/theorems/68f377b5-ebfb-4968-8151-b5878c9a360a
-- title:
--   Theorem 6.11 — the conjugate of a sum of M-concave functions is the real (integer) convolution of their conjugates
-- statement:
--   Let $V$ be a finite nonempty set and $B_1,B_2\subseteq\mathbb Z^V$ finite integral base sets (finite nonempty sets satisfying the exchange axiom (B1)). Let $\omega_1:B_1\to\mathbb R$ and $\omega_2:B_2\to\mathbb R$ satisfy the exchange property (EXC), and suppose $B_1\cap B_2\neq\emptyset$. Let $\omega_1+\omega_2:B_1\cap B_2\to\mathbb R$ be the pointwise sum, and for a function $g$ on a finite set $B$ let $g^\circ(p)=\min\{\langle p,x\rangle-g(x)\mid x\in B\}$ be its concave conjugate. Then
--   $$(\omega_1+\omega_2)^\circ(p)=\sup\{\omega_1^\circ(p_1)+\omega_2^\circ(p_2)\mid p_1+p_2=p,\ p_1,p_2\in\mathbb R^V\}\qquad(p\in\mathbb R^V),\tag{6.18}$$
--   the conjugate of $\omega_1+\omega_2$ being taken with respect to $B_1\cap B_2$. If, in addition, $\omega_1$ and $\omega_2$ are integer-valued, then
--   $$(\omega_1+\omega_2)^\circ(p)=\sup\{\omega_1^\circ(p_1)+\omega_2^\circ(p_2)\mid p_1+p_2=p,\ p_1,p_2\in\mathbb Z^V\}\qquad(p\in\mathbb Z^V).\tag{6.19}$$
--
--   The identity (6.18) is the dual counterpart of the trivial identity $(\omega_1\square\omega_2)^\circ=\omega_1^\circ+\omega_2^\circ$; unlike it, it rests on the Fenchel-type duality theorem. Note that $\omega_1+\omega_2$ need not satisfy (EXC).
--
--   **Formalization Note.** Both sides are compared in `EReal`: the left side is a real number (coerced), and the right sides are the `EReal` suprema `realConjConv` and `intConjConv`, so the identities include the assertion that the suprema are finite. Integer-valuedness is stated only on each function's own domain.
--
--   Differences from the source:
--   - reading: splitting vectors written "p₁ ∈ R, p₂ ∈ R" (resp. "∈ Z") → p₁, p₂ range over ℝ^V (resp. ℤ^V); reason: p₁ + p₂ = p with p ∈ ℝ^V forces vectors; the page's "R" is shorthand for R^V
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 303, Theorem 6.11 (Eqs. (6.18), (6.19))

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Exchange
import Definitions.Def_SteinitzExchange_Duality_Conjugate
import Definitions.Def_SteinitzExchange_Duality_Supplement_ConjugateConvolution

namespace SteinitzExchange.Duality.Supplement

/-- Murota 1996, p. 303, Theorem 6.11. Let `B₁, B₂ ⊆ ℤ^V` be finite integral base sets. If
`ω₁ : B₁ → ℝ` and `ω₂ : B₂ → ℝ` satisfy (EXC) and `B₁ ∩ B₂ ≠ ∅`, then the concave conjugate of
`ω₁ + ω₂ : B₁ ∩ B₂ → ℝ` equals `ω₁° □_ℝ ω₂°` on `ℝ^V` (Eq. (6.18)). If, in addition, `ω₁` and
`ω₂` are integer-valued, then `(ω₁ + ω₂)° = ω₁° □_ℤ ω₂°` on `ℤ^V` (Eq. (6.19)). -/
theorem conj_sum_eq_conv {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B₁ B₂ : Finset (V → ℤ)) (hB₁ : IsIntegralBaseSet B₁) (hB₂ : IsIntegralBaseSet B₂)
    (ω₁ ω₂ : (V → ℤ) → ℝ) (hω₁ : SatisfiesEXC B₁ ω₁) (hω₂ : SatisfiesEXC B₂ ω₂)
    (hne : (B₁ ∩ B₂).Nonempty) :
    (∀ p : V → ℝ,
      ((concaveConj (B₁ ∩ B₂) (fun x => ω₁ x + ω₂ x) p : ℝ) : EReal) =
        realConjConv B₁ ω₁ B₂ ω₂ p) ∧
    ((∀ x ∈ B₁, ∃ k : ℤ, ω₁ x = k) → (∀ x ∈ B₂, ∃ k : ℤ, ω₂ x = k) →
      ∀ p : V → ℤ,
        ((concaveConj (B₁ ∩ B₂) (fun x => ω₁ x + ω₂ x) (toReal p) : ℝ) : EReal) =
          intConjConv B₁ ω₁ B₂ ω₂ p) := by sorry

end SteinitzExchange.Duality.Supplement
