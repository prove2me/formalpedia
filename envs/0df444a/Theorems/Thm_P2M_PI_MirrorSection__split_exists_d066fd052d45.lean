-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__split_exists_d066fd052d45
-- name    : P2M_PI_MirrorSection__split_exists_d066fd052d45
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:58:12.639786+00:00
-- url     : https://prove2.me/theorems/0f2c9206-9e16-4cce-a76e-0a0a7b34cd6a
-- title:
--   P2 M PI Mirror Section  split exists d066fd052d45: P2 M PI Mirror Section  split exists d066fd052d45
-- statement:
--   The P2 M PI Mirror Section  split exists d066fd052d45 construction uses the P2 M PI Mirror Section  split exists d066fd052d45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L150-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L150-L164

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

theorem P2M_PI_MirrorSection__split_exists_d066fd052d45 (hLS : LowSplit) {P : Matrix (Fin m) (Fin m) ℂ} (hP : IsMonomial P) (hPd : IsUnit P.det)
    {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ UTset m) :
    ∃ a v : Matrix (Fin m) (Fin m) ℂ, a ∈ UTset m ∧ v ∈ UTset m ∧ P * a * P⁻¹ ∈ LTset m ∧
      P * v * P⁻¹ ∈ UTset m ∧ u = a * v := by sorry

alias «PI».«MirrorSection₂».«split_exists» := P2M_PI_MirrorSection__split_exists_d066fd052d45
