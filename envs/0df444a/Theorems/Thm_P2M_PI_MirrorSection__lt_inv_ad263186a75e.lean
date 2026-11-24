-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__lt_inv_ad263186a75e
-- name    : P2M_PI_MirrorSection__lt_inv_ad263186a75e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:59:57.18538+00:00
-- url     : https://prove2.me/theorems/7488114a-7416-4171-93ac-c7da4d4487c5
-- title:
--   P2 M PI Mirror Section  lt inv ad263186a75e: P2 M PI Mirror Section  lt inv ad263186a75e
-- statement:
--   The P2 M PI Mirror Section  lt inv ad263186a75e construction uses the P2 M PI Mirror Section  lt inv ad263186a75e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L78-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L78-L88

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

theorem P2M_PI_MirrorSection__lt_inv_ad263186a75e {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ LTset m) :
    l * l⁻¹ = 1 ∧ l⁻¹ * l = 1 ∧ l⁻¹ ∈ LTset m := by sorry

alias «PI».«MirrorSection₂».«lt_inv» := P2M_PI_MirrorSection__lt_inv_ad263186a75e
