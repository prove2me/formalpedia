-- Prove2me | Theorems.Thm_PI_WGL_io_eig_sep
-- name    : PI.WGL.io_eig_sep
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:00:19.482887+00:00
-- url     : https://prove2.me/theorems/efd630e2-b27c-548b-beb8-3fce8ea56d59
-- title:
--   WGL: io eig sep
-- statement:
--   The WGL construction uses the io eig sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoExistsOfCap.lean#L109-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoExistsOfCap.lean#L109-L133

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_PeriodIntegrals_GTBranch
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoExistsOfCap
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
open Formalism.BasicNotions MvPolynomial

theorem PI.WGL.io_eig_sep {ι V : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    (C : ℂ → Module.End ℂ V) (p : ι → ℂ → ℂ) (i0 : ι) (hp : ∀ i, i ≠ i0 → ∃ u, p i u ≠ p i0 u) :
    ∀ (F : Finset ι) (y : ι → V), (∀ i ∈ F, ∀ u, C u (y i) = p i u • y i) →
      (∀ u, C u (∑ i ∈ F, y i) = p i0 u • ∑ i ∈ F, y i) →
      ∑ i ∈ F, y i = ∑ i ∈ F.filter (fun i => i = i0), y i := by sorry
