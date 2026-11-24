-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__uh_inv_11c75eae1df9
-- name    : P2M_PI_MirrorSection__uh_inv_11c75eae1df9
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:56:03.072701+00:00
-- url     : https://prove2.me/theorems/56bb336a-ed12-48a9-818c-f55ce7929d10
-- title:
--   P2 M PI Mirror Section  uh inv 11c75eae1df9: P2 M PI Mirror Section  uh inv 11c75eae1df9
-- statement:
--   The P2 M PI Mirror Section  uh inv 11c75eae1df9 construction uses the P2 M PI Mirror Section  uh inv 11c75eae1df9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L39-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L39-L52

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

theorem P2M_PI_MirrorSection__uh_inv_11c75eae1df9 {a : B.Mat k r} (ha : a ∈ UH (Hpk k r)) :
    a * a⁻¹ = 1 ∧ a⁻¹ * a = 1 ∧ a⁻¹ ∈ UH (Hpk k r) := by sorry

alias «PI».«MirrorSection₂».«uh_inv» := P2M_PI_MirrorSection__uh_inv_11c75eae1df9
