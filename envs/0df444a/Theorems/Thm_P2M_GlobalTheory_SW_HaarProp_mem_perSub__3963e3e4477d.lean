-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_HaarProp_mem_perSub__3963e3e4477d
-- name    : P2M_GlobalTheory_SW_HaarProp_mem_perSub__3963e3e4477d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:58.133203+00:00
-- url     : https://prove2.me/theorems/f269284d-5fc1-46f0-bdcc-3ac02e1dd001
-- title:
--   P2 M Global Theory SW Haar Prop mem per Sub  3963e3e4477d: P2 M Global Theory SW Haar Prop mem per Sub  3963e3e4477d
-- statement:
--   The P2 M Global Theory SW Haar Prop mem per Sub  3963e3e4477d construction uses the P2 M Global Theory SW Haar Prop mem per Sub  3963e3e4477d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatRationalCoordsIntegralProportional.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatRationalCoordsIntegralProportional.lean#L13-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatRationalCoordsIntegralProportional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarProp
open HaarLevel

theorem P2M_GlobalTheory_SW_HaarProp_mem_perSub__3963e3e4477d {K κ ι : Type} [Field K] (R : ℕ) (x : Matrix κ ι K) :
    x ∈ perSub K κ ι R ↔ ∃ y, IntM y ∧ R • y = x := by sorry

alias «GlobalTheory».«SW».«HaarProp».«mem_perSub'» := P2M_GlobalTheory_SW_HaarProp_mem_perSub__3963e3e4477d
