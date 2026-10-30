-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_realHilbertSchmidtProjection
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.realHilbertSchmidtProjection
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:44:15.842687+00:00
-- url     : https://prove2.me/theorems/9ef1c368-9553-423d-843a-3d00f327ecda
-- title:
--   Lemma III.3: real Hilbert–Schmidt projection
-- statement:
--   Let $H$ be a closed subgroup of $\mathrm{GL}(N,\mathbb C)$, where $N>0$, and let $\mathfrak h$ be its real Lie algebra. Suppose $h_1,\ldots,h_m$ form a real orthonormal basis for $\langle A,B\rangle=\operatorname{Re}\operatorname{tr}(A^\dagger B)$. For every complex matrix $g$, the unique orthogonal projections onto $\mathfrak h$ and its real orthogonal complement are
--   $$P g=\sum_{j=1}^m\operatorname{Re}\operatorname{tr}(h_j^\dagger g)h_j,\qquad P^\perp g=g-Pg.$$
--   The domain consists of all complex matrices regarded as a real vector space; the formula does not discard the real part.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 22, Lemma III.3: real Hilbert–Schmidt projection

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Lemma III.3(a,b), PDF p.22: projections onto the actual real subgroup
algebra and its orthogonal complement, including uniqueness. -/
theorem realHilbertSchmidtProjection {n m : ℕ} (hn : 0 < n)
    (H : Subgroup ((Matrix (Fin n) (Fin n) ℂ))ˣ) (hH : IsClosed (H : Set ((Matrix (Fin n) (Fin n) ℂ))ˣ)) (b : Fin m → (Matrix (Fin n) (Fin n) ℂ))
    (hspan : (Submodule.span ℝ (Set.range b) : Set ((Matrix (Fin n) (Fin n) ℂ))) = matrixLieSet H)
    (horth : ∀ i j, realHSPairing (b i) (b j) = if i = j then 1 else 0) :
    ∀ g : (Matrix (Fin n) (Fin n) ℂ),
      (∃! p, IsHSProjection (matrixLieSet H) g p) ∧
      IsHSProjection (matrixLieSet H) g (basisProjection b g) ∧
      (∃! p, IsHSProjection (hsOrthogonal (matrixLieSet H)) g p) ∧
      IsHSProjection (hsOrthogonal (matrixLieSet H)) g (g - basisProjection b g) := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
