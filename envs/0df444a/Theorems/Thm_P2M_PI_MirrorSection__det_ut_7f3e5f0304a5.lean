-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__det_ut_7f3e5f0304a5
-- name    : P2M_PI_MirrorSection__det_ut_7f3e5f0304a5
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:00:13.792513+00:00
-- url     : https://prove2.me/theorems/3cc1856e-3148-470f-a18e-f0fa3efd5ff9
-- title:
--   P2 M PI Mirror Section  det ut 7f3e5f0304a5: P2 M PI Mirror Section  det ut 7f3e5f0304a5
-- statement:
--   The P2 M PI Mirror Section  det ut 7f3e5f0304a5 construction uses the P2 M PI Mirror Section  det ut 7f3e5f0304a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L46-L48

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_IsMonomialConjTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.MirrorSection₂
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}

theorem P2M_PI_MirrorSection__det_ut_7f3e5f0304a5 {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ UTset m) : u.det = 1 := by sorry

alias «PI».«MirrorSection₂».«det_ut» := P2M_PI_MirrorSection__det_ut_7f3e5f0304a5
