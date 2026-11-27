-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_mul_aee82e1fd007
-- name    : P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_mul_aee82e1fd007
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:45.130613+00:00
-- url     : https://prove2.me/theorems/d14ca1a7-01d8-5c3a-b3d7-bc42ecd4b98b
-- title:
--   P2 M Ground Theory Global Semi Local tensor Equiv  tmul mul aee82e1fd007: P2 M Ground Theory Global Semi Local tensor Equiv  tmul mul aee82e1fd007
-- statement:
--   The P2 M Ground Theory Global Semi Local tensor Equiv  tmul mul aee82e1fd007 construction uses the P2 M Ground Theory Global Semi Local tensor Equiv  tmul mul aee82e1fd007 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Finite.lean#L121-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Finite.lean#L121-L124

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

theorem P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_mul_aee82e1fd007 (a : v.adicCompletion K) (y : L ⊗[K] v.adicCompletion K) :
    tensorEquiv' L v ((1 ⊗ₜ a) * y) =
      algebraMap (v.adicCompletion K) (CompletionsOver L v) a * tensorEquiv' L v y := by sorry

alias «GroundTheory».«Global».«SemiLocal».«tensorEquiv'_tmul_mul» := P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_mul_aee82e1fd007
