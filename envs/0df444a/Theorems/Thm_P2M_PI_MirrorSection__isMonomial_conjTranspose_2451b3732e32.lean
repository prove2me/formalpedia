-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__isMonomial_conjTranspose_2451b3732e32
-- name    : P2M_PI_MirrorSection__isMonomial_conjTranspose_2451b3732e32
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:57:12.285851+00:00
-- url     : https://prove2.me/theorems/954381f4-b360-4539-a835-5f91cfc4bd59
-- title:
--   P2 M PI Mirror Section  is Monomial conj Transpose 2451b3732e32: P2 M PI Mirror Section  is Monomial conj Transpose 2451b3732e32
-- statement:
--   The P2 M PI Mirror Section  is Monomial conj Transpose 2451b3732e32 construction uses the P2 M PI Mirror Section  is Monomial conj Transpose 2451b3732e32 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L108-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L108-L111

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

theorem P2M_PI_MirrorSection__isMonomial_conjTranspose_2451b3732e32 {P : Matrix (Fin m) (Fin m) ℂ} (hP : IsMonomial P) : IsMonomial Pᴴ := by sorry

alias «PI».«MirrorSection₂».«isMonomial_conjTranspose» := P2M_PI_MirrorSection__isMonomial_conjTranspose_2451b3732e32
