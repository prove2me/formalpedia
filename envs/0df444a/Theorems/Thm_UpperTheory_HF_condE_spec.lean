-- Prove2me | Theorems.Thm_UpperTheory_HF_condE_spec
-- name    : UpperTheory.HF.condE_spec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:03:40.191888+00:00
-- url     : https://prove2.me/theorems/a58a05bf-fe28-493f-a082-ddf1d3861c9e
-- title:
--   HF: cond E spec
-- statement:
--   The HF construction uses the cond E spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/CondESpec.lean#L9-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/CondESpec.lean#L9-L35

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_ImgOneGcd
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CondESpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.condE_spec :
    ∀ {φ : Frame} (H : HostRaw φ), H.condE ∣ H.condN ∧ 0 < H.condE ∧ ∀ f : ℕ, f ∣ H.condN → (H.imgOne f = ⊥ ↔ H.condE ∣ f) := by sorry
