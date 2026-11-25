-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_SplitGL_hermitian_map_snd
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL.hermitian_map_snd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:34.827349+00:00
-- url     : https://prove2.me/theorems/228cfd1c-e4ee-4d2f-914d-cce1b89f139e
-- title:
--   Split GL: hermitian map snd
-- statement:
--   The Split GL construction uses the hermitian map snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/SplitGL.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/SplitGL.lean#L60-L63

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL.hermitian_map_snd (J : Matrix n n R) (hJ : Formalism.UG.cT σ J = J) : J.map (p2 π) = (J.map (p1 π))ᵀ := by sorry
