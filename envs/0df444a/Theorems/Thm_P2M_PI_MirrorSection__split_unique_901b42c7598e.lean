-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__split_unique_901b42c7598e
-- name    : P2M_PI_MirrorSection__split_unique_901b42c7598e
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:57:02.082805+00:00
-- url     : https://prove2.me/theorems/713bf2e7-3f65-5e2e-b08f-75edbf37fb42
-- title:
--   P2 M PI Mirror Section  split unique 901b42c7598e: P2 M PI Mirror Section  split unique 901b42c7598e
-- statement:
--   The P2 M PI Mirror Section  split unique 901b42c7598e construction uses the P2 M PI Mirror Section  split unique 901b42c7598e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L113-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L113-L148

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

theorem P2M_PI_MirrorSection__split_unique_901b42c7598e {P : Matrix (Fin m) (Fin m) ℂ} (hP : IsUnit P.det)
    {a₁ a₂ v₁ v₂ : Matrix (Fin m) (Fin m) ℂ}
    (ha₁ : P * a₁ * P⁻¹ ∈ LTset m) (ha₂ : P * a₂ * P⁻¹ ∈ LTset m)
    (hv₁ : P * v₁ * P⁻¹ ∈ UTset m) (hv₂ : P * v₂ * P⁻¹ ∈ UTset m)
    (h : a₁ * v₁ = a₂ * v₂) : a₁ = a₂ := by sorry

alias «PI».«MirrorSection₂».«split_unique» := P2M_PI_MirrorSection__split_unique_901b42c7598e
