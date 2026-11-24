-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__ut_inv_c3f594f8935a
-- name    : P2M_PI_MirrorSection__ut_inv_c3f594f8935a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:00:06.853362+00:00
-- url     : https://prove2.me/theorems/cdc00109-1c4c-42c6-86e7-720ffe6bb0bd
-- title:
--   P2 M PI Mirror Section  ut inv c3f594f8935a: P2 M PI Mirror Section  ut inv c3f594f8935a
-- statement:
--   The P2 M PI Mirror Section  ut inv c3f594f8935a construction uses the P2 M PI Mirror Section  ut inv c3f594f8935a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L60-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L60-L76

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

theorem P2M_PI_MirrorSection__ut_inv_c3f594f8935a {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ UTset m) :
    u * u⁻¹ = 1 ∧ u⁻¹ * u = 1 ∧ u⁻¹ ∈ UTset m := by sorry

alias «PI».«MirrorSection₂».«ut_inv» := P2M_PI_MirrorSection__ut_inv_c3f594f8935a
