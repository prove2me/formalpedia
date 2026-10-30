-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_cb_entropy_dimension_bounds
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.cb_entropy_dimension_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:46:10.715964+00:00
-- url     : https://prove2.me/theorems/8ca813e5-c5be-4bed-a394-bc22b18969d2
-- title:
--   (5.2): dimension bounds and extremal channels
-- statement:
--   Let $\Phi:M_d\to M_d$ be any CPT map, $d\ge1$. For minimal CB entropy in nats,
--
--   $$-\log d\le S_{\mathrm{CB,min}}(\Phi)\le\log d.$$
--
--   The identity channel attains the lower bound, and the completely noisy channel $\mathcal N(X)=(\operatorname{Tr}X)I_d/d$ attains the upper bound:
--
--   $$S_{\mathrm{CB,min}}(\mathrm{id}_d)=-\log d,\qquad S_{\mathrm{CB,min}}(\mathcal N)=\log d.$$
--
--   For $d=1$ both bounds are zero. This is the sound dimension bound, independently of the source's unpinned marginal bound (5.1).
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 22, (5.2): dimension bounds and extremal channels

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P16

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Advance50.P16

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact frozen counterparts; their bodies and conventions were checked for this repair.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P19 (flip)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Support50.P11 (wernerHolevoChannel)

/-- (5.2), PDF pp.22–23: dimension bounds and both extremal channels, including d=1. -/
theorem cb_entropy_dimension_bounds {I : Type} [Fintype I] [Nonempty I]
    (Phi : (Mat I →ₗ[ℂ] Mat I)) (hPhi : IsChannel Phi) :
    -Real.log (Fintype.card I) ≤ minCBEntropy Phi ∧
    minCBEntropy Phi ≤ Real.log (Fintype.card I) ∧
    minCBEntropy (LinearMap.id : (Mat I →ₗ[ℂ] Mat I)) = -Real.log (Fintype.card I) ∧
    minCBEntropy (fun X : Mat I => ((Fintype.card I : ℂ)⁻¹) • (X.trace • (1 : Mat I))) =
      Real.log (Fintype.card I) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
