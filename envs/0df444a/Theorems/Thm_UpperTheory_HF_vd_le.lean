-- Prove2me | Theorems.Thm_UpperTheory_HF_vd_le
-- name    : UpperTheory.HF.vd_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:31:47.225886+00:00
-- url     : https://prove2.me/theorems/4710f3f1-6f54-43e0-b3d9-2a38cb8f01af
-- title:
--   HF: vd le
-- statement:
--   The HF construction uses the vd le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/VdLe.lean#L42-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/VdLe.lean#L42-L89

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdFormula
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LayerBot
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdLe
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

theorem UpperTheory.HF.vd_le :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → H.vdH l ≤ (H.sl l : ℝ) - 1 / ((l : ℝ) - 1) ∧ H.vdH l ≤ (H.condE.factorization l : ℝ) := by sorry
