-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__n_mul_f9b46a5d1768
-- name    : P2M_PI_MirrorSection__n_mul_f9b46a5d1768
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:57:04.501483+00:00
-- url     : https://prove2.me/theorems/edada553-f9c5-4a8f-a068-d19fd460ef99
-- title:
--   P2 M PI Mirror Section  n mul f9b46a5d1768: P2 M PI Mirror Section  n mul f9b46a5d1768
-- statement:
--   The P2 M PI Mirror Section  n mul f9b46a5d1768 construction uses the P2 M PI Mirror Section  n mul f9b46a5d1768 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L295-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L295-L331

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

theorem P2M_PI_MirrorSection__n_mul_f9b46a5d1768 {n m : B.Mat k r} (hn : n ∈ Nset k r) (hm : m ∈ Nset k r) : n * m ∈ Nset k r := by sorry

alias «PI».«MirrorSection₂».«n_mul» := P2M_PI_MirrorSection__n_mul_f9b46a5d1768
