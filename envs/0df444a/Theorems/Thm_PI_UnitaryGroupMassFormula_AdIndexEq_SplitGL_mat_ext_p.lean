-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_SplitGL_mat_ext_p
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL.mat_ext_p
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:51:17.210249+00:00
-- url     : https://prove2.me/theorems/67bd1ce1-f005-48c6-8d94-ec297a5061e1
-- title:
--   Split GL: mat ext p
-- statement:
--   The Split GL construction uses the mat ext p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/SplitGL.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/SplitGL.lean#L19-L22

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL.mat_ext_p (π : R ≃+* k × k) {M N : Matrix n n R} (h1 : M.map (p1 π) = N.map (p1 π))
    (h2 : M.map (p2 π) = N.map (p2 π)) : M = N := by sorry
