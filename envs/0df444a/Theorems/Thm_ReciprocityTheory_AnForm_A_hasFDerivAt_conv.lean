-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_hasFDerivAt_conv
-- name    : ReciprocityTheory.AnForm.A.hasFDerivAt_conv
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:05:36.749839+00:00
-- url     : https://prove2.me/theorems/301e9c37-8a52-41dc-9ec8-6971978dec3a
-- title:
--   A: has FDeriv At conv
-- statement:
--   The A construction uses the has FDeriv At conv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollA.lean#L88-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollA.lean#L88-L105

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Convolution
noncomputable section
variable {D : ℕ}
variable (ρ : Mollifier D)

theorem ReciprocityTheory.AnForm.A.hasFDerivAt_conv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ε : ℝ} (hε : 0 < ε) {g : (Fin D → ℂ) → F} (hcg : HasCompactSupport g) (hg : ContDiff ℝ 1 g)
    (x : Fin D → ℂ) :
    HasFDerivAt (fun x => ∫ t, ρ.scaled ε t • g (x - t))
      (∫ t, ρ.scaled ε t • fderiv ℝ g (x - t)) x := by sorry
