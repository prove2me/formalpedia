-- Prove2me | Theorems.Thm_PI_ScRefExists_GWG_hyp_dvd
-- name    : PI.ScRefExists.GWG.hyp_dvd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:26:05.314436+00:00
-- url     : https://prove2.me/theorems/dd074969-0817-5073-a6fd-4587bc991ef5
-- title:
--   GWG: hyp dvd
-- statement:
--   The GWG construction uses the hyp dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/GWGlue.lean#L251-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/GWGlue.lean#L251-L267

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

theorem PI.ScRefExists.GWG.hyp_dvd {I : Formalism.MainNotions.S.AutInst} {g g' r k : ℕ} {θ : 𝓞 I.E} {e f : Fin r → Fin I.n → I.E} {M : ℕ}
    (h : Hyp I g r k θ e f M) (hd : g' ∣ g) (h1 : 1 ≤ g') : Hyp I g' r k θ e f M := by sorry
