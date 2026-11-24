-- Prove2me | Theorems.Thm_PI_ScRefExists_WB_mem_WA
-- name    : PI.ScRefExists.WB.mem_WA
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:54:10.62646+00:00
-- url     : https://prove2.me/theorems/d007429a-7830-4ed2-8402-94ff2fe11eb1
-- title:
--   WB: mem WA
-- statement:
--   The WB construction uses the mem WA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/WeilBasisExistence.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/WeilBasisExistence.lean#L37-L38

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HGZeroRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PrincipalIdealRingAtPrime
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WeilBasisExistence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open PI PI.ScRefExists PI.ScRefExists.WB
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.ScRefExists.WB.mem_WA {p r : ℕ} {e f : Fin r → Fin I.n → I.E} {x : Fin I.n → I.E} :
    x ∈ WA I p r e f ↔ x ∈ LA I p ∧ ∀ a, hG I (e a) x = 0 ∧ hG I (f a) x = 0 := by sorry
