-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__onto_low_16ac7e56a491
-- name    : P2M_PI_MirrorSection__onto_low_16ac7e56a491
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:57:42.949603+00:00
-- url     : https://prove2.me/theorems/cbb202c2-4f24-41dc-b12b-a9f7ade5f72c
-- title:
--   P2 M PI Mirror Section  onto low 16ac7e56a491: P2 M PI Mirror Section  onto low 16ac7e56a491
-- statement:
--   The P2 M PI Mirror Section  onto low 16ac7e56a491 construction uses the P2 M PI Mirror Section  onto low 16ac7e56a491 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L87-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L87-L99

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

theorem P2M_PI_MirrorSection__onto_low_16ac7e56a491 {g : B.Mat k r} (hg : g⁻¹ * g = 1) {a : ℕ} (hmaps : ∀ y ∈ lowS k r a, g *ᵥ y ∈ lowS k r a) :
    ∀ y ∈ lowS k r a, ∃ x ∈ lowS k r a, g *ᵥ x = y := by sorry

alias «PI».«MirrorSection₂».«onto_low» := P2M_PI_MirrorSection__onto_low_16ac7e56a491
