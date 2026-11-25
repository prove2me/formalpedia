-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Cj_inG_diag
-- name    : PI.VolSemiDirect.W.Cj.inG_diag
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:35:22.127562+00:00
-- url     : https://prove2.me/theorems/a44033c0-f76e-4906-a7c1-d4655e4f9e26
-- title:
--   Cj: in G diag
-- statement:
--   The Cj construction uses the in G diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/GlGeneratedTransvectionsDiag.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/GlGeneratedTransvectionsDiag.lean#L36-L41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_GlGeneratedTransvectionsDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open Matrix
variable {A : Type} [CommRing A] {k : ℕ}

theorem PI.VolSemiDirect.W.Cj.inG_diag (d : Fin k → A) (hd : ∀ i, IsUnit (d i)) : InG (diagonal d) := by sorry
