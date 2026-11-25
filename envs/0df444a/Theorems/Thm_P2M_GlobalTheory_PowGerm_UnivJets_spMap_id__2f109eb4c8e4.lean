-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PowGerm_UnivJets_spMap_id__2f109eb4c8e4
-- name    : P2M_GlobalTheory_PowGerm_UnivJets_spMap_id__2f109eb4c8e4
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:53.408383+00:00
-- url     : https://prove2.me/theorems/3ce53919-04dd-499f-95cd-3cd7e1a7d4c9
-- title:
--   P2 M Global Theory Pow Germ Univ Jets sp Map id  2f109eb4c8e4: P2 M Global Theory Pow Germ Univ Jets sp Map id  2f109eb4c8e4
-- statement:
--   The P2 M Global Theory Pow Germ Univ Jets sp Map id  2f109eb4c8e4 construction uses the P2 M Global Theory Pow Germ Univ Jets sp Map id  2f109eb4c8e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UniversalStatement.lean#L132-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UniversalStatement.lean#L132-L134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SurjectiveOfKerLeMapSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalStatement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_zR_mem_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PowGerm.UnivJets
variable {V : Type} [CommRing V] {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
open Chart (JetR zR jetAug_zR jet_ext ker_jetAug_pow zR_mem_ker jetTruncR dualLift dualLift_zR fstD kerD_sq)

theorem P2M_GlobalTheory_PowGerm_UnivJets_spMap_id__2f109eb4c8e4 (A : Type) [CommRing A] [Algebra V A] : Chart.spMap (AlgHom.id V A) = 𝟙 _ := by sorry

alias «GlobalTheory».«PowGerm».«UnivJets».«spMap_id'» := P2M_GlobalTheory_PowGerm_UnivJets_spMap_id__2f109eb4c8e4
