-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Cj_inG_rowT
-- name    : PI.VolSemiDirect.W.Cj.inG_rowT
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:36:04.569132+00:00
-- url     : https://prove2.me/theorems/91f1932e-3fbc-526f-a948-edcb445771c6
-- title:
--   Cj: in G row T
-- statement:
--   The Cj construction uses the in G row T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/GlGeneratedTransvectionsDiag.lean#L43-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/GlGeneratedTransvectionsDiag.lean#L43-L59

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

theorem PI.VolSemiDirect.W.Cj.inG_rowT (p : Fin k) (c : Fin k → A) (s : Finset (Fin k)) (hp : p ∉ s) :
    InG (1 + ∑ i ∈ s, single p i (c i)) := by sorry
