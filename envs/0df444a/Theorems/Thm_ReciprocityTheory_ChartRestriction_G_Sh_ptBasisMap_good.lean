-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptBasisMap_good
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.ptBasisMap_good
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:09.389415+00:00
-- url     : https://prove2.me/theorems/d46afd2a-995e-53d7-a991-12e042479dcb
-- title:
--   Sh: pt Basis Map good
-- statement:
--   The Sh construction uses the pt Basis Map good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtBasisMapGood.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtBasisMapGood.lean#L51-L56

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.ptBasisMap_good (G : LogFGL v d) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) : PTGood v (ptBasisMap G γ) := by sorry
