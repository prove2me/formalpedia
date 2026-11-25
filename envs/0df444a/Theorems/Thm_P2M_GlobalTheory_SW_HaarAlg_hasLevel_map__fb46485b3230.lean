-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_HaarAlg_hasLevel_map__fb46485b3230
-- name    : P2M_GlobalTheory_SW_HaarAlg_hasLevel_map__fb46485b3230
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:54.200894+00:00
-- url     : https://prove2.me/theorems/04039e95-4bc7-4cc6-adb8-f6072599282d
-- title:
--   P2 M Global Theory SW Haar Alg has Level map  fb46485b3230: P2 M Global Theory SW Haar Alg has Level map  fb46485b3230
-- statement:
--   The P2 M Global Theory SW Haar Alg has Level map  fb46485b3230 construction uses the P2 M Global Theory SW Haar Alg has Level map  fb46485b3230 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RationalSchwartzBruhatAlgebraIntegralLinear.lean#L33-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RationalSchwartzBruhatAlgebraIntegralLinear.lean#L33-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarAlg
variable {K : Type} [Field K] {κ ι : Type}

theorem P2M_GlobalTheory_SW_HaarAlg_hasLevel_map__fb46485b3230 {R : ℕ} {φ ψ : Matrix κ ι K → ℂ} (h1 : HasLevel R φ) (h2 : HasLevel R ψ)
    (f : ℂ → ℂ → ℂ) (hf : f 0 0 = 0) : HasLevel R fun x => f (φ x) (ψ x) := by sorry

alias «GlobalTheory».«SW».«HaarAlg».«hasLevel_map₂» := P2M_GlobalTheory_SW_HaarAlg_hasLevel_map__fb46485b3230
