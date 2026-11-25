-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_ck_Rw__802bba5733f4
-- name    : P2M_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_ck_Rw__802bba5733f4
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:54:45.980324+00:00
-- url     : https://prove2.me/theorems/5feb720d-359f-4aec-b74c-e68d81b4b964
-- title:
--   P2 M Formalism Fourier Decay Alt P Cut BP Limit Normal Forms ck Rw  802bba5733f4: P2 M Formalism Fourier Decay Alt P Cut BP Limit Normal Forms ck Rw  802bba5733f4
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Cut BP Limit Normal Forms ck Rw  802bba5733f4 construction uses the P2 M Formalism Fourier Decay Alt P Cut BP Limit Normal Forms ck Rw  802bba5733f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/OpLocal.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/OpLocal.lean#L40-L45

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UsCompose
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ContDiff Topology
set_option linter.unusedSectionVars false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E₁ E₂ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]

theorem P2M_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_ck_Rw__802bba5733f4 {m : ℕ∞} {UU : Set (Mat k r)} {w : List (Mat k r)} (hw : ∀ X ∈ w, inLie k r X)
    {f : Mat k r → E₁} (hf : CkOn (m + w.length) UU f) : CkOn m UU (Rw w f) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«CutBP».«LimitNormalForms».«ck_Rw'» := P2M_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_ck_Rw__802bba5733f4
