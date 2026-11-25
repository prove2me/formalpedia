-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__ut_mul_7638fd5817a9
-- name    : P2M_PI_MirrorSection__ut_mul_7638fd5817a9
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:57:32.356011+00:00
-- url     : https://prove2.me/theorems/cfccd1a8-1bd4-4e94-b6f0-6249bace7e8d
-- title:
--   P2 M PI Mirror Section  ut mul 7638fd5817a9: P2 M PI Mirror Section  ut mul 7638fd5817a9
-- statement:
--   The P2 M PI Mirror Section  ut mul 7638fd5817a9 construction uses the P2 M PI Mirror Section  ut mul 7638fd5817a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L14-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L14-L28

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

theorem P2M_PI_MirrorSection__ut_mul_7638fd5817a9 {a b : Matrix (Fin m) (Fin m) ℂ} (ha : a ∈ UTset m) (hb : b ∈ UTset m) : a * b ∈ UTset m := by sorry

alias «PI».«MirrorSection₂».«ut_mul» := P2M_PI_MirrorSection__ut_mul_7638fd5817a9
