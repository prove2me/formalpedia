-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_symplectic_rank_bounds_invariance
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.symplectic_rank_bounds_invariance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:56:42.471779+00:00
-- url     : https://prove2.me/theorems/4843c55d-7aca-4fce-8158-0d0565bbd9c9
-- title:
--   §III (3.6)–(3.8): symplectic rank bounds and invariance
-- statement:
--   Let $n\ge1$ and let $V$ be a real vector space of dimension $2n$, with a nondegenerate alternating bilinear form $B$. For a subspace $W$, put $k=\dim W$, let $r(W)$ be the rank of $B|_{W\times W}$, and put $W^\perp=\{x:B(w,x)=0\text{ for all }w\in W\}$.
--
--   $$
--   r(W)\in2\mathbb N,\qquad\max\{0,2(k-n)\}\le r(W)\le k,\qquad r(FW)=r(W).
--   $$
--
--   The last equality holds for every linear automorphism preserving B. Equal-dimensional subspaces with unequal restricted ranks cannot be related by such an automorphism. These bounds distinguish symplectic subspaces intrinsically.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 8, §III (3.6)–(3.8): symplectic rank bounds and invariance

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF pp.8–9, (3.6)–(3.8): even rank, sharp dimension bounds, and
invariance under symplectic automorphisms, hence obstruction to mapping subspaces. -/
theorem symplectic_rank_bounds_invariance (n : ℕ) (hn : 0 < n)
    (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 2 * n) (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (W : Submodule ℝ V) :
    Even (symplecticRank B W) ∧ symplecticRank B W ≤ Module.finrank ℝ W ∧
    max (0 : ℤ) (2 * ((Module.finrank ℝ W : ℤ) - (n : ℤ))) ≤ (symplecticRank B W : ℤ) ∧
    (∀ f : V ≃ₗ[ℝ] V, (∀ x y, B (f x) (f y) = B x y) →
      symplecticRank B (W.map f.toLinearMap) = symplecticRank B W) ∧
    (∀ Wprime : Submodule ℝ V,
      Module.finrank ℝ Wprime = Module.finrank ℝ W →
      symplecticRank B Wprime ≠ symplecticRank B W →
        ¬ ∃ f : V ≃ₗ[ℝ] V, (∀ x y, B (f x) (f y) = B x y) ∧
          W.map f.toLinearMap = Wprime) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
