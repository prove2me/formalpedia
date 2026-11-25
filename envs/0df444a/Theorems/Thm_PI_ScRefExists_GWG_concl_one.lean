-- Prove2me | Theorems.Thm_PI_ScRefExists_GWG_concl_one
-- name    : PI.ScRefExists.GWG.concl_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:24:57.737799+00:00
-- url     : https://prove2.me/theorems/d46f61e0-9aa9-5a2a-89d7-768488da635a
-- title:
--   GWG: concl one
-- statement:
--   The GWG construction uses the concl one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/GWGlue.lean#L269-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/GWGlue.lean#L269-L283

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GlobWIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GWGlue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GWG
open PI.ScRefExists.Sk

theorem PI.ScRefExists.GWG.concl_one (I : Formalism.MainNotions.S.AutInst) (r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ) :
    Concl I 1 r k θ e f M := by sorry
