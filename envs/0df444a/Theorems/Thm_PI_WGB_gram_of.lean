-- Prove2me | Theorems.Thm_PI_WGB_gram_of
-- name    : PI.WGB.gram_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:45:22.120318+00:00
-- url     : https://prove2.me/theorems/439c2e27-78f2-4be4-b140-fdd3c73d18d7
-- title:
--   WGB: gram of
-- statement:
--   The WGB construction uses the gram of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/TransposeConjComm.lean#L14-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/TransposeConjComm.lean#L14-L25

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_TransposeConjComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)

theorem PI.WGB.gram_of {n k : ℕ} {f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ} (κ : Fin n → ℕ) (hκ : Antitone κ)
    (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (hT : ∀ t : Fin n → ℂˣ, rowAct ℂ (iotaC ℂ n k (Matrix.diagonal fun i => (t i : ℂ))).transpose f =
      (∏ i, (t i : ℂ) ^ κ i) • f)
    (g g' : Matrix (Fin n) (Fin n) ℂ) :
    fockF (rowAct ℂ (iotaC ℂ n k g).transpose f) (rowAct ℂ (iotaC ℂ n k g').transpose f) =
      fockF f f * hwAt κ (g'.conjTranspose * g) := by sorry
