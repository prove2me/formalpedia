-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_finsum_fib
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.finsum_fib
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:00:16.204066+00:00
-- url     : https://prove2.me/theorems/3da1b58a-6e3f-54b0-a924-4e3ec7a64ea7
-- title:
--   Gen: finsum fib
-- statement:
--   The Gen construction uses the finsum fib property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStB.lean#L325-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStB.lean#L325-L329

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω} {e : Fin (D + 1) → ι}
variable [DecidableEq ι] (G : Gen x e) {w : Fin (D + 1) → ℂ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.finsum_fib (hx0 : x (e 0) ≠ 0) (hw : G.Good w) (f : (ι → ℂ) → ℂ) :
    ∑ᶠ z ∈ fib x e w, f z = ((G.P.map (deh w 0)).roots.map fun ρ => f (G.zOf w ρ)).sum := by sorry
