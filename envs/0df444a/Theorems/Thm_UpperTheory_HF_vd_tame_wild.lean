-- Prove2me | Theorems.Thm_UpperTheory_HF_vd_tame_wild
-- name    : UpperTheory.HF.vd_tame_wild
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:03:26.95681+00:00
-- url     : https://prove2.me/theorems/e49cecbb-f5ef-48c0-b2f2-747542ea86eb
-- title:
--   HF: vd tame wild
-- statement:
--   The HF construction uses the vd tame wild property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/VdTameWild.lean#L24-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/VdTameWild.lean#L24-L127

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdFormula
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LayerBot
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CardImgOneDvd
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MemRam
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdTameWild
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

theorem UpperTheory.HF.vd_tame_wild :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → (¬ l ∣ H.el l → H.vdH l = 1 - 1 / (H.el l : ℝ)) ∧ (l ∣ H.el l → 1 ≤ H.vdH l) ∧ (¬ l ∣ H.el l → H.sl l = 1) := by sorry
