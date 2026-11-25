-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__n_inv_2b0268f7044c
-- name    : P2M_PI_MirrorSection__n_inv_2b0268f7044c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:57:41.220902+00:00
-- url     : https://prove2.me/theorems/87efc62c-ab76-57ff-9304-8cbb4f6afca8
-- title:
--   P2 M PI Mirror Section  n inv 2b0268f7044c: P2 M PI Mirror Section  n inv 2b0268f7044c
-- statement:
--   The P2 M PI Mirror Section  n inv 2b0268f7044c construction uses the P2 M PI Mirror Section  n inv 2b0268f7044c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L101-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L101-L146

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

theorem P2M_PI_MirrorSection__n_inv_2b0268f7044c {n : B.Mat k r} (hn : n ∈ Nset k r) : n⁻¹ ∈ Nset k r := by sorry

alias «PI».«MirrorSection₂».«n_inv» := P2M_PI_MirrorSection__n_inv_2b0268f7044c
