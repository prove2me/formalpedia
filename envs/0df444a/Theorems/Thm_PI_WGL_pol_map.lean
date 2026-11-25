-- Prove2me | Theorems.Thm_PI_WGL_pol_map
-- name    : PI.WGL.pol_map
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:46:56.037799+00:00
-- url     : https://prove2.me/theorems/7cd36324-0979-4be6-ad11-5215c152b349
-- title:
--   WGL: pol map
-- statement:
--   The WGL construction uses the pol map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/CapelliOps.lean#L115-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/CapelliOps.lean#L115-L118

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRaise
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem PI.WGL.pol_map {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) {r m : ℕ} (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin m) R) :
    pol S a b (MvPolynomial.map ψ f) = MvPolynomial.map ψ (pol R a b f) := by sorry
