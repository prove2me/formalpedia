-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ThetaAmple_prod_level__1175cbb17ff8
-- name    : P2M_GlobalTheory_ThetaAmple_prod_level__1175cbb17ff8
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:11:02.451834+00:00
-- url     : https://prove2.me/theorems/fffda2c9-008a-4a90-a378-2b1c050567f1
-- title:
--   P2 M Global Theory Theta Ample prod level  1175cbb17ff8: P2 M Global Theory Theta Ample prod level  1175cbb17ff8
-- statement:
--   The P2 M Global Theory Theta Ample prod level  1175cbb17ff8 construction uses the P2 M Global Theory Theta Ample prod level  1175cbb17ff8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/RelAmpleThetaBundleProjectiveModel.lean#L243-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/RelAmpleThetaBundleProjectiveModel.lean#L243-L246

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_RelAmpleThetaBundleProjectiveModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaAmple

theorem P2M_GlobalTheory_ThetaAmple_prod_level__1175cbb17ff8 {N : ℕ} (w α : ℂ) (F F' : Fin N → ℂ) (hα : α ^ N = eC (-(N : ℂ) * w))
    (hF : ∀ k, F' k = α * eC (-(N : ℂ) * w) * F k) :
    ∏ k, F' k = eC (-((N * (N + 1) : ℕ) : ℂ) * w) * ∏ k, F k := by sorry

alias «GlobalTheory».«ThetaAmple».«prod_level'» := P2M_GlobalTheory_ThetaAmple_prod_level__1175cbb17ff8
