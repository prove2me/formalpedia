-- Prove2me | Theorems.Thm_UpperTheory_HF_inert_q
-- name    : UpperTheory.HF.inert_q
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:26:18.055377+00:00
-- url     : https://prove2.me/theorems/3fa13033-4c48-4f16-a78a-8148af0279ff
-- title:
--   HF: inert q
-- statement:
--   The HF construction uses the inert q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/inertQ.lean#L99-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/inertQ.lean#L99-L125

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdTameWild
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MemRam
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_inertQ
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

theorem UpperTheory.HF.inert_q :
    ∀ {φ : Frame} (H : HostAx φ), H.el H.q ≤ 2 ∧ H.sl H.q = 1 ∧ (H.q ∈ H.ram → H.el H.q = 2 ∧ H.vdH H.q = 1 / 2 ∧ H.condE.factorization H.q = 1) ∧ (H.q ∉ H.ram → H.vdH H.q = 0) ∧ (H.PsQ → H.q ∈ H.ram) := by sorry
