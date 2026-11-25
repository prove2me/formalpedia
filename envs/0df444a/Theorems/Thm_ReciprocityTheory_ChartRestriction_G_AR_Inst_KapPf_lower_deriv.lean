-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_KapPf_lower_deriv
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf.lower_deriv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:56:38.862931+00:00
-- url     : https://prove2.me/theorems/bb2f503f-2fc0-4a09-b2da-6e9c4b5f09c8
-- title:
--   Kap Pf: lower deriv
-- statement:
--   The Kap Pf construction uses the lower deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/HasFDerivAtNmat.lean#L62-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/HasFDerivAtNmat.lean#L62-L126

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetOfBlockDiag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_HasFDerivAtNmat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates Matrix Topology Filter
open scoped Classical
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf.lower_deriv (τ : X.Ψ) (A : Matrix (Fin r) (Fin r) ℂ) (U : Set (V (nd X))) (hU : IsOpen U)
    (Φ : V (nd X) → V (nd X)) (bf : V (nd X) → Matrix (Fin r) (Fin r) ℂ)
    (hrel : ∀ z ∈ U, mat (nmat X (Φ z)) τ * bf z = A * mat (nmat X z) τ)
    (hup : ∀ z ∈ U, ∀ a c : Fin r, c < a → bf z a c = 0)
    (z : V (nd X)) (hz : z ∈ U) (Φ' : V (nd X) →L[ℂ] V (nd X)) (hΦ : HasFDerivAt Φ Φ' z)
    (h : V (nd X)) (a c : Fin r) (hca : c < a) :
    (bf z * (Ring.inverse (mat (nmat X z) τ) * Lin X τ h) -
      (Ring.inverse (mat (nmat X (Φ z)) τ) * Lin X τ (Φ' h)) * bf z) a c = 0 := by sorry
