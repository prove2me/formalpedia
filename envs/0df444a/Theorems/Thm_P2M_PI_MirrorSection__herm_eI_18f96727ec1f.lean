-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__herm_eI_18f96727ec1f
-- name    : P2M_PI_MirrorSection__herm_eI_18f96727ec1f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:57:29.633748+00:00
-- url     : https://prove2.me/theorems/d83a3191-772e-4838-b9c1-f39a3fa26a2e
-- title:
--   P2 M PI Mirror Section  herm e I 18f96727ec1f: P2 M PI Mirror Section  herm e I 18f96727ec1f
-- statement:
--   The P2 M PI Mirror Section  herm e I 18f96727ec1f construction uses the P2 M PI Mirror Section  herm e I 18f96727ec1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L193-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L193-L196

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

theorem P2M_PI_MirrorSection__herm_eI_18f96727ec1f (y : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) y (bvec (eI k r b)) = y (esI k r b) := by sorry

alias «PI».«MirrorSection₂».«herm_eI» := P2M_PI_MirrorSection__herm_eI_18f96727ec1f
