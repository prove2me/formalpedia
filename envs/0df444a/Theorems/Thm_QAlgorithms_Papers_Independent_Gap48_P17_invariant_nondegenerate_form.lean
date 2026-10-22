-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_invariant_nondegenerate_form
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.invariant_nondegenerate_form
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:59:25.679592+00:00
-- url     : https://prove2.me/theorems/36cea443-02d9-43bb-ab60-7d0ef2346d48
-- title:
--   Lemma 1.5
-- statement:
--   Let $V=\mathbb R^{p,q}$ be nonzero with its nondegenerate metric, and let $S$ be a finite-dimensional irreducible real module for $\operatorname{Cl}(V,-g)$. Restrict $S$ to the spin action of $\mathfrak{so}(V)$. There is a real bilinear form $\beta$ on the full module $S$ such that
--   $$\beta\text{ is nondegenerate and }\mathfrak{so}(V)\text{-invariant}.$$
--   This supplies a duality on the full spinor, including cases with two semispinor summands.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 13, Lemma 1.5

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Lemma 1.5, PDF pp. 13--14: existence is a conclusion, not a self-duality hypothesis. -/
theorem invariant_nondegenerate_form (p q : ℕ) (hd : 0 < p + q)
    (S : Type*) [AddCommGroup S] [Module ℝ S] [FiniteDimensional ℝ S]
    (rho : SpinRepresentation (signatureMatrix p q) S) :
    ∃ b : LinearMap.BilinForm ℝ S, b ∈ invariantForms rho ∧ b.Nondegenerate := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
