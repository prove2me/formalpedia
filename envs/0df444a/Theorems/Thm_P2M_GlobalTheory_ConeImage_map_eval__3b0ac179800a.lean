-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ConeImage_map_eval__3b0ac179800a
-- name    : P2M_GlobalTheory_ConeImage_map_eval__3b0ac179800a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:23.34118+00:00
-- url     : https://prove2.me/theorems/ffb7be19-6b25-497f-b4f4-ae37828bc3e9
-- title:
--   P2 M Global Theory Cone Image map eval  3b0ac179800a: P2 M Global Theory Cone Image map eval  3b0ac179800a
-- statement:
--   The P2 M Global Theory Cone Image map eval  3b0ac179800a construction uses the P2 M Global Theory Cone Image map eval  3b0ac179800a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsNhdsSubsetRange.lean#L111-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsNhdsSubsetRange.lean#L111-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsNhdsSubsetRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ConeImage

theorem P2M_GlobalTheory_ConeImage_map_eval__3b0ac179800a {σ A : Type*} [CommRing A] [Algebra ℂ A] (j : MvPolynomial σ ℂ →ₐ[ℂ] A)
    (φ : A →ₐ[ℂ] ℂ) (r : MvPolynomial σ ℂ) :
    φ (j r) = MvPolynomial.eval (fun i => φ (j (MvPolynomial.X i))) r := by sorry

alias «GlobalTheory».«ConeImage».«map_eval₂» := P2M_GlobalTheory_ConeImage_map_eval__3b0ac179800a
