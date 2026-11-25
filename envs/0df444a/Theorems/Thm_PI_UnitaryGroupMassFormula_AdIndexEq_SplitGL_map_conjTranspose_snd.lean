-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_SplitGL_map_conjTranspose_snd
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL.map_conjTranspose_snd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:39:39.426325+00:00
-- url     : https://prove2.me/theorems/5eefed73-c351-4b51-b18b-946a9755d469
-- title:
--   Split GL: map conj Transpose snd
-- statement:
--   The Split GL construction uses the map conj Transpose snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/SplitGL.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/SplitGL.lean#L41-L43

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL
open Matrix
variable {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
variable (σ : R →+* R) (π : R ≃+* k × k) (hπ : ∀ r, π (σ r) = (π r).swap)
include hπ

theorem PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL.map_conjTranspose_snd (M : Matrix n n R) : (Formalism.UG.cT σ M).map (p2 π) = (M.map (p1 π))ᵀ := by sorry
