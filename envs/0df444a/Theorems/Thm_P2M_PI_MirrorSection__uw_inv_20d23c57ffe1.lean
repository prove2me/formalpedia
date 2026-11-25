-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__uw_inv_20d23c57ffe1
-- name    : P2M_PI_MirrorSection__uw_inv_20d23c57ffe1
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:39:26.049949+00:00
-- url     : https://prove2.me/theorems/67814f63-8aa9-4948-9d11-0c91151423dc
-- title:
--   P2 M PI Mirror Section  uw inv 20d23c57ffe1: P2 M PI Mirror Section  uw inv 20d23c57ffe1
-- statement:
--   The P2 M PI Mirror Section  uw inv 20d23c57ffe1 construction uses the P2 M PI Mirror Section  uw inv 20d23c57ffe1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L219-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L219-L225

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

theorem P2M_PI_MirrorSection__uw_inv_20d23c57ffe1 {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by sorry

alias «PI».«MirrorSection₂».«uw_inv» := P2M_PI_MirrorSection__uw_inv_20d23c57ffe1
