-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__ut_conjTranspose_65da1bf78ca4
-- name    : P2M_PI_MirrorSection__ut_conjTranspose_65da1bf78ca4
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:00:10.209175+00:00
-- url     : https://prove2.me/theorems/8d296520-ab6e-40eb-8339-e4de59b3cfea
-- title:
--   P2 M PI Mirror Section  ut conj Transpose 65da1bf78ca4: P2 M PI Mirror Section  ut conj Transpose 65da1bf78ca4
-- statement:
--   The P2 M PI Mirror Section  ut conj Transpose 65da1bf78ca4 construction uses the P2 M PI Mirror Section  ut conj Transpose 65da1bf78ca4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L50-L53

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

theorem P2M_PI_MirrorSection__ut_conjTranspose_65da1bf78ca4 {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ UTset m) : uᴴ ∈ LTset m := by sorry

alias «PI».«MirrorSection₂».«ut_conjTranspose» := P2M_PI_MirrorSection__ut_conjTranspose_65da1bf78ca4
