-- Prove2me | Theorems.Thm_PI_QnHermHaar_rel_herm_unitary
-- name    : PI.QnHermHaar.rel_herm_unitary
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:39:34.721507+00:00
-- url     : https://prove2.me/theorems/032312ff-c459-46a4-880a-f27fb734fae9
-- title:
--   Qn Herm Haar: rel herm unitary
-- statement:
--   The Qn Herm Haar construction uses the rel herm unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RestrictedGramHermitianInvolution.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RestrictedGramHermitianInvolution.lean#L60-L64

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RestrictedGramHermitianInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem PI.QnHermHaar.rel_herm_unitary {n : ℕ} (H g : Matrix (Fin n) (Fin n) ℂ) (hU : gᴴ * H * g = H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by sorry
