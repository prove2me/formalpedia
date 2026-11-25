-- Prove2me | Theorems.Thm_P2M_GlobalTheory_BoxCosetSum_continuous_evalV__bc2f1c713454
-- name    : P2M_GlobalTheory_BoxCosetSum_continuous_evalV__bc2f1c713454
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:16.522027+00:00
-- url     : https://prove2.me/theorems/c03f9ad8-d1a7-46a7-b179-cfd477dd1ed0
-- title:
--   P2 M Global Theory Box Coset Sum continuous eval V  bc2f1c713454: P2 M Global Theory Box Coset Sum continuous eval V  bc2f1c713454
-- statement:
--   The P2 M Global Theory Box Coset Sum continuous eval V  bc2f1c713454 construction uses the P2 M Global Theory Box Coset Sum continuous eval V  bc2f1c713454 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScalingOpenSubgroupsFinite.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScalingOpenSubgroupsFinite.lean#L13-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScalingOpenSubgroupsFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.BoxCosetSum
variable {F : Type} [Field F] [NumberField F]

theorem P2M_GlobalTheory_BoxCosetSum_continuous_evalV__bc2f1c713454 (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) := by sorry

alias «GlobalTheory».«BoxCosetSum».«continuous_evalV'» := P2M_GlobalTheory_BoxCosetSum_continuous_evalV__bc2f1c713454
