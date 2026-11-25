-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__uw_mul_58b4297bf430
-- name    : P2M_PI_MirrorSection__uw_mul_58b4297bf430
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:57:48.897352+00:00
-- url     : https://prove2.me/theorems/7b7300cb-7eb3-40f0-9679-45f08cb0d92f
-- title:
--   P2 M PI Mirror Section  uw mul 58b4297bf430: P2 M PI Mirror Section  uw mul 58b4297bf430
-- statement:
--   The P2 M PI Mirror Section  uw mul 58b4297bf430 construction uses the P2 M PI Mirror Section  uw mul 58b4297bf430 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L227-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L227-L232

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

theorem P2M_PI_MirrorSection__uw_mul_58b4297bf430 {z : Fin (2 * r + k + 1) → ℂ} {a b : B.Mat k r} (ha : a ∈ UWset k r z) (hb : b ∈ UWset k r z) :
    a * b ∈ UWset k r z := by sorry

alias «PI».«MirrorSection₂».«uw_mul» := P2M_PI_MirrorSection__uw_mul_58b4297bf430
