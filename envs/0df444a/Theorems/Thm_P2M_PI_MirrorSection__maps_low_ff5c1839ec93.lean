-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__maps_low_ff5c1839ec93
-- name    : P2M_PI_MirrorSection__maps_low_ff5c1839ec93
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:38:43.228719+00:00
-- url     : https://prove2.me/theorems/d7ae5e4e-9919-4859-8591-9ad710477a9d
-- title:
--   P2 M PI Mirror Section  maps low ff5c1839ec93: P2 M PI Mirror Section  maps low ff5c1839ec93
-- statement:
--   The P2 M PI Mirror Section  maps low ff5c1839ec93 construction uses the P2 M PI Mirror Section  maps low ff5c1839ec93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L72-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L72-L85

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

theorem P2M_PI_MirrorSection__maps_low_ff5c1839ec93 {n : B.Mat k r} (hn : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      n i (eI k r a) = if i = eI k r a then 1 else 0) {a : ℕ} (har : a ≤ r) :
    ∀ y ∈ lowS k r a, n *ᵥ y ∈ lowS k r a := by sorry

alias «PI».«MirrorSection₂».«maps_low» := P2M_PI_MirrorSection__maps_low_ff5c1839ec93
