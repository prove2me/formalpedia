-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_invariant_form_dimensions
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.invariant_form_dimensions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:06:11.736064+00:00
-- url     : https://prove2.me/theorems/3beee649-8fd2-4075-a29c-5839bec0a341
-- title:
--   Corollary 1.15
-- statement:
--   For a nonzero real signature $(p,q)$, let $B_{p,q}$ be the invariant real bilinear forms on the full spinor and $C_{p,q}$ its real Schur algebra. Their dimensions agree, and for $s=p-q$ modulo eight,
--   $$\dim_{\mathbb R} B_{p,q}=\dim_{\mathbb R}C_{p,q}=b(s),\qquad\begin{array}{c|cccccccc}s&1&2&3&4&5&6&7&0\\\hline b(s)&4&8&4&8&4&2&1&2\end{array}$$
--   The function has period eight and the mirror symmetry $(p,q)\mapsto(8k-q,8k-p)$. For the full complex spinor in positive complex dimension $d$,
--   $$\dim_{\mathbb C}B_d=\dim_{\mathbb C}C_d=\begin{cases}2,&d\text{ even},\\1,&d\text{ odd}.\end{cases}$$
--   These are dimensions of actual invariant subspaces, not assigned dimensions of tabulated models.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 17, Corollary 1.15

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Corollary 1.15, PDF p. 17: actual real and complex dimensions, periodicity and mirror. -/
theorem invariant_form_dimensions :
    (∀ (p q : ℕ), 0 < p + q →
      ∀ (S : Type) [AddCommGroup S] [Module ℝ S] [FiniteDimensional ℝ S]
        (rho : SpinRepresentation (signatureMatrix p q) S),
        Module.finrank ℝ (invariantForms rho) = Module.finrank ℝ (schurAlgebra rho) ∧
        Module.finrank ℝ (invariantForms rho) = realFormDimensionTable ((p : ℤ) - q)) ∧
    (∀ s : ℤ, realFormDimensionTable (s + 8) = realFormDimensionTable s) ∧
    (∀ p q k : ℕ, p ≤ 8 * k → q ≤ 8 * k →
      realFormDimensionTable ((p : ℤ) - q) =
        realFormDimensionTable (((8 * k - q : ℕ) : ℤ) - (8 * k - p : ℕ))) ∧
    (∀ (d : ℕ), 0 < d →
      ∀ (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
        (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S),
        Module.finrank ℂ (invariantForms rho) = Module.finrank ℂ (schurAlgebra rho) ∧
        Module.finrank ℂ (invariantForms rho) = if Even d then 2 else 1) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
