-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_ker
-- name    : PI.UnitaryGroupMassFormula.LCG.ap_ker
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:02:40.469978+00:00
-- url     : https://prove2.me/theorems/4621bbe9-fbea-49c1-ad97-bccc7f87abe8
-- title:
--   LCG: ap ker
-- statement:
--   The LCG construction uses the ap ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L202-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L202-L256

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.UnitaryGroupMassFormula.LCG.ap_ker (δ : Matrix (Fin I.n) (Fin I.n) I.E) (k : ℕ) (u b' : Fin k → Fin I.n → I.E)
    (hu : LinearIndependent I.E (fun c => δ *ᵥ u c))
    (hsp : ∀ z, δ *ᵥ z ∈ Submodule.span I.E (Set.range fun c => δ *ᵥ u c))
    (hb : LinearIndependent I.E b') (hperp : ∀ a, PerpKer I δ (b' a)) :
    ∀ w, hM I b' *ᵥ w = 0 → δ *ᵥ w = 0 := by sorry
