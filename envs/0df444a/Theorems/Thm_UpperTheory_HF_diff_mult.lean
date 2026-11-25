-- Prove2me | Theorems.Thm_UpperTheory_HF_diff_mult
-- name    : UpperTheory.HF.diff_mult
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:19:45.748122+00:00
-- url     : https://prove2.me/theorems/5ee745d2-e0f2-5d59-be0a-e44d78368389
-- title:
--   HF: diff mult
-- statement:
--   The HF construction uses the diff mult property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/DiffMult.lean#L11-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/DiffMult.lean#L11-L52

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_GrpBridge
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdTameWild
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDifferentExponentDenominator
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffMult
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

theorem UpperTheory.HF.diff_mult :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) = H.el l * H.vdH l ∧ multiplicity P (span {(l : 𝓞 H.E)}) = H.el l ∧ (¬ l ∣ H.el l → multiplicity P (differentIdeal ℤ (𝓞 H.E)) = H.el l - 1) ∧ (l ∣ H.el l → H.el l ≤ multiplicity P (differentIdeal ℤ (𝓞 H.E))) := by sorry
