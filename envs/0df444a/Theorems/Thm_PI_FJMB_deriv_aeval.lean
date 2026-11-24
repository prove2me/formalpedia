-- Prove2me | Theorems.Thm_PI_FJMB_deriv_aeval
-- name    : PI.FJMB.deriv_aeval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:45.217536+00:00
-- url     : https://prove2.me/theorems/72871e8b-c943-40e6-b72e-51409733de84
-- title:
--   FJMB: deriv aeval
-- statement:
--   The FJMB construction uses the deriv aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurChain.lean#L28-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurChain.lean#L28-L52

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurChain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMB
variable {R : Type*} [CommRing R] {σ : Type*}

theorem PI.FJMB.deriv_aeval {B : Type*} [CommRing B] [Algebra R B] (D : Derivation R B B) (φ : σ → B)
    (S : Finset σ) (hS : ∀ v, v ∉ S → D (φ v) = 0) (f : MvPolynomial σ R) :
    D (aeval φ f) = ∑ v ∈ S, aeval φ (pderiv v f) * D (φ v) := by sorry
