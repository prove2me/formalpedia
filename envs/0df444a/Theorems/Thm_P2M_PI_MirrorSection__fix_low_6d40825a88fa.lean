-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__fix_low_6d40825a88fa
-- name    : P2M_PI_MirrorSection__fix_low_6d40825a88fa
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:57:51.639484+00:00
-- url     : https://prove2.me/theorems/3ba0cd59-8858-48a0-93d5-087ab647b3ea
-- title:
--   P2 M PI Mirror Section  fix low 6d40825a88fa: P2 M PI Mirror Section  fix low 6d40825a88fa
-- statement:
--   The P2 M PI Mirror Section  fix low 6d40825a88fa construction uses the P2 M PI Mirror Section  fix low 6d40825a88fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L148-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L148-L169

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

theorem P2M_PI_MirrorSection__fix_low_6d40825a88fa {g : B.Mat k r} (hfix : ∀ b : Fin r, g *ᵥ bvec (eI k r b) = bvec (eI k r b)) {a : ℕ}
    (har : a ≤ r) : ∀ y ∈ lowS k r a, g *ᵥ y = y := by sorry

alias «PI».«MirrorSection₂».«fix_low» := P2M_PI_MirrorSection__fix_low_6d40825a88fa
