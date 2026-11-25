-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__lt_mul_a8f5782a03d1
-- name    : P2M_PI_MirrorSection__lt_mul_a8f5782a03d1
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:57:10.546024+00:00
-- url     : https://prove2.me/theorems/e41a7a62-98ba-45cf-9ed6-86a3dfaece2f
-- title:
--   P2 M PI Mirror Section  lt mul a8f5782a03d1: P2 M PI Mirror Section  lt mul a8f5782a03d1
-- statement:
--   The P2 M PI Mirror Section  lt mul a8f5782a03d1 construction uses the P2 M PI Mirror Section  lt mul a8f5782a03d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L30-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L30-L44

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

theorem P2M_PI_MirrorSection__lt_mul_a8f5782a03d1 {a b : Matrix (Fin m) (Fin m) ℂ} (ha : a ∈ LTset m) (hb : b ∈ LTset m) : a * b ∈ LTset m := by sorry

alias «PI».«MirrorSection₂».«lt_mul» := P2M_PI_MirrorSection__lt_mul_a8f5782a03d1
