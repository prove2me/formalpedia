-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartResidueDegree_length_quotient_eq_one_0714608bd97e
-- name    : P2M_GroundTheory_Heights__Heights_ChartResidueDegree_length_quotient_eq_one_0714608bd97e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:36.995377+00:00
-- url     : https://prove2.me/theorems/b0134d91-fac7-4939-bd90-576d9dd1d1c4
-- title:
--   P2 M Ground Theory Heights  Heights Chart Residue Degree length quotient eq one 0714608bd97e: P2 M Ground Theory Heights  Heights Chart Residue Degree length quotient eq one 0714608bd97e
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Residue Degree length quotient eq one 0714608bd97e construction uses the P2 M Ground Theory Heights  Heights Chart Residue Degree length quotient eq one 0714608bd97e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartResidueDegree.lean#L114-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartResidueDegree.lean#L114-L130

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartResidueDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartResidueDegree

theorem P2M_GroundTheory_Heights__Heights_ChartResidueDegree_length_quotient_eq_one_0714608bd97e {O R : Type*} [CommRing O] [CommRing R] [Algebra O R] (𝔓 : Ideal R)
    (hmax : (𝔓.comap (algebraMap O R)).IsMaximal) (hsurj : ∀ x : R, ∃ o : O, x - algebraMap O R o ∈ 𝔓) :
    Module.length O (R ⧸ 𝔓) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartResidueDegree».«length_quotient_eq_one» := P2M_GroundTheory_Heights__Heights_ChartResidueDegree_length_quotient_eq_one_0714608bd97e
