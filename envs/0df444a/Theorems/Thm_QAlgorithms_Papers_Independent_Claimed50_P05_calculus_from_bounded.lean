-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_from_bounded
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_from_bounded
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:15:18.426455+00:00
-- url     : https://prove2.me/theorems/a5907e13-05d8-406e-ab9a-320f75caf98d
-- title:
--   Theorem 6.1
-- statement:
--   Let $(X,\Sigma)$ be measurable and $H$ a Hilbert space. Suppose $L:M_b(X)\to L(H)$ is a unital $k$-linear star homomorphism that is weakly continuous for bounded-pointwise convergence. For $f\in M(X)$ put $e=(1+|f|)^{-1}$ and define
--
--   $$\widetilde L(f)=L(e)^{-1}L(ef).$$
--
--   Both symbols supplied to $L$ are bounded, and the inverse is understood as a graph inverse on the range. This computed map is a measurable calculus, agrees with $L$ on bounded symbols, and every measurable calculus agreeing there is equal to it.
--
--   This is the canonical unique extension from bounded to all measurable symbols.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 25, Theorem 6.1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

/-- Theorem 6.1, PDF p.25: the computed extension exists and is the unique measurable extension. -/
theorem calculus_from_bounded (L : BoundedSymbols X k → H →L[k] H)
    (hL : BoundedHom L) (hbp : BoundedWeakBP L) :
    Calculus (algebraicExtension L) ∧
    (∀ f : BoundedSymbols X k, algebraicExtension L f.val = boundedGraph (L f)) ∧
    ∀ F : Symbol X k → Relation H, Calculus F →
      (∀ f : BoundedSymbols X k, F f.val = boundedGraph (L f)) → F = algebraicExtension L := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
