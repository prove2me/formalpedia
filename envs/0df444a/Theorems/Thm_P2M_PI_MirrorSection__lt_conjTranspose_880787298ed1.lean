-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__lt_conjTranspose_880787298ed1
-- name    : P2M_PI_MirrorSection__lt_conjTranspose_880787298ed1
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:00:31.751797+00:00
-- url     : https://prove2.me/theorems/8632c04e-8080-4442-aa11-b3bc915c5dbb
-- title:
--   P2 M PI Mirror Section  lt conj Transpose 880787298ed1: P2 M PI Mirror Section  lt conj Transpose 880787298ed1
-- statement:
--   The P2 M PI Mirror Section  lt conj Transpose 880787298ed1 construction uses the P2 M PI Mirror Section  lt conj Transpose 880787298ed1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L55-L58

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

theorem P2M_PI_MirrorSection__lt_conjTranspose_880787298ed1 {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ LTset m) : lᴴ ∈ UTset m := by sorry

alias «PI».«MirrorSection₂».«lt_conjTranspose» := P2M_PI_MirrorSection__lt_conjTranspose_880787298ed1
