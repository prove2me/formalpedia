-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptBasisMap_inv
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.ptBasisMap_inv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:15:32.005916+00:00
-- url     : https://prove2.me/theorems/b1ee6bc3-0ac0-43f5-99bd-2c5e0d0e8183
-- title:
--   Sh: pt Basis Map inv
-- statement:
--   The Sh construction uses the pt Basis Map inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtBasisMapGood.lean#L95-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtBasisMapGood.lean#L95-L152

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtRescaleGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtBasisMapGood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Sh.ptBasisMap_inv (G : LogFGL v d) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (hdet : v (Matrix.det (Matrix.of fun a b => tangent (γ a) b)) = 0) :
    ∃ Ψ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (Ψ a)) ∧
      (∀ a, constantCoeff (Ψ a) = 0) ∧
      (∀ a, subst Ψ (ptBasisMap G γ a) = X a) ∧ (∀ a, subst (ptBasisMap G γ) (Ψ a) = X a) := by sorry
