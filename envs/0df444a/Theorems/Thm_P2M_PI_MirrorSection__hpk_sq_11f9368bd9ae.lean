-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__hpk_sq_11f9368bd9ae
-- name    : P2M_PI_MirrorSection__hpk_sq_11f9368bd9ae
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:57:30.896693+00:00
-- url     : https://prove2.me/theorems/77d448c6-0c1d-4a9f-8db6-7119524fcf73
-- title:
--   P2 M PI Mirror Section  hpk sq 11f9368bd9ae: P2 M PI Mirror Section  hpk sq 11f9368bd9ae
-- statement:
--   The P2 M PI Mirror Section  hpk sq 11f9368bd9ae construction uses the P2 M PI Mirror Section  hpk sq 11f9368bd9ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L16-L29

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
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
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}

theorem P2M_PI_MirrorSection__hpk_sq_11f9368bd9ae (k r : ℕ) : Hpk k r * Hpk k r = 1 := by sorry

alias «PI».«MirrorSection₂».«hpk_sq» := P2M_PI_MirrorSection__hpk_sq_11f9368bd9ae
