-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__uw_inWb_121488a2cc3d
-- name    : P2M_PI_MirrorSection__uw_inWb_121488a2cc3d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:57:29.239736+00:00
-- url     : https://prove2.me/theorems/cb95d122-5602-4f40-89ac-95117b9bb8e2
-- title:
--   P2 M PI Mirror Section  uw in Wb 121488a2cc3d: P2 M PI Mirror Section  uw in Wb 121488a2cc3d
-- statement:
--   The P2 M PI Mirror Section  uw in Wb 121488a2cc3d construction uses the P2 M PI Mirror Section  uw in Wb 121488a2cc3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L198-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L198-L217

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

theorem P2M_PI_MirrorSection__uw_inWb_121488a2cc3d {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z)
    {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : inWb k r (h *ᵥ v) := by sorry

alias «PI».«MirrorSection₂».«uw_inWb» := P2M_PI_MirrorSection__uw_inWb_121488a2cc3d
