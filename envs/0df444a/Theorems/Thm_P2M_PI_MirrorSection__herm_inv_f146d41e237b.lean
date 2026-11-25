-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__herm_inv_f146d41e237b
-- name    : P2M_PI_MirrorSection__herm_inv_f146d41e237b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:57:19.892794+00:00
-- url     : https://prove2.me/theorems/d68cdcff-de8d-49e6-85a8-4e41a17d6fb1
-- title:
--   P2 M PI Mirror Section  herm inv f146d41e237b: P2 M PI Mirror Section  herm inv f146d41e237b
-- statement:
--   The P2 M PI Mirror Section  herm inv f146d41e237b construction uses the P2 M PI Mirror Section  herm inv f146d41e237b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L171-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L171-L176

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

theorem P2M_PI_MirrorSection__herm_inv_f146d41e237b {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (h *ᵥ x) (h *ᵥ y) = herm (Hpk k r) x y := by sorry

alias «PI».«MirrorSection₂».«herm_inv» := P2M_PI_MirrorSection__herm_inv_f146d41e237b
