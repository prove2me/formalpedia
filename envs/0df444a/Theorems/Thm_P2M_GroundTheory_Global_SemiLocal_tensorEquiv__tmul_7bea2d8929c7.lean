-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- name    : P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:11:21.945802+00:00
-- url     : https://prove2.me/theorems/37e83036-a78b-49bd-8b52-c35453d6aa0c
-- title:
--   P2 M Ground Theory Global Semi Local tensor Equiv  tmul 7bea2d8929c7: P2 M Ground Theory Global Semi Local tensor Equiv  tmul 7bea2d8929c7
-- statement:
--   The P2 M Ground Theory Global Semi Local tensor Equiv  tmul 7bea2d8929c7 construction uses the P2 M Ground Theory Global Semi Local tensor Equiv  tmul 7bea2d8929c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Finite.lean#L116-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Finite.lean#L116-L119

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Approximation
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (L) (v : HeightOneSpectrum (𝓞 K))

theorem P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7 (x : L) (a : v.adicCompletion K) :
    tensorEquiv' L v (x ⊗ₜ a) =
      algebraMap L (CompletionsOver L v) x * algebraMap (v.adicCompletion K) _ a := by sorry

alias «GroundTheory».«Global».«SemiLocal».«tensorEquiv'_tmul» := P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
