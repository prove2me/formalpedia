-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__n_on_Wb_19802610ecc0
-- name    : P2M_PI_MirrorSection__n_on_Wb_19802610ecc0
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:57:12.529344+00:00
-- url     : https://prove2.me/theorems/c210b86b-8014-428b-b550-9aa9027ef92d
-- title:
--   P2 M PI Mirror Section  n on Wb 19802610ecc0: P2 M PI Mirror Section  n on Wb 19802610ecc0
-- statement:
--   The P2 M PI Mirror Section  n on Wb 19802610ecc0 construction uses the P2 M PI Mirror Section  n on Wb 19802610ecc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L234-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L234-L247

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

theorem P2M_PI_MirrorSection__n_on_Wb_19802610ecc0 {n : B.Mat k r} (hn : n ∈ Nset k r) {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) :
    n *ᵥ u - u ∈ lowS k r r := by sorry

alias «PI».«MirrorSection₂».«n_on_Wb» := P2M_PI_MirrorSection__n_on_Wb_19802610ecc0
