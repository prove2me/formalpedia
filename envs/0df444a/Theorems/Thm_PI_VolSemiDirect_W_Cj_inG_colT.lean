-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Cj_inG_colT
-- name    : PI.VolSemiDirect.W.Cj.inG_colT
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:35:32.050485+00:00
-- url     : https://prove2.me/theorems/f2f00423-5df9-45a8-9c8d-efb4990c19e0
-- title:
--   Cj: in G col T
-- statement:
--   The Cj construction uses the in G col T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/GlGeneratedTransvectionsDiag.lean#L61-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/GlGeneratedTransvectionsDiag.lean#L61-L78

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

theorem PI.VolSemiDirect.W.Cj.inG_colT (p : Fin k) (c : Fin k → A) (s : Finset (Fin k)) (hp : p ∉ s) :
    InG (1 + ∑ i ∈ s, single i p (c i)) := by sorry
