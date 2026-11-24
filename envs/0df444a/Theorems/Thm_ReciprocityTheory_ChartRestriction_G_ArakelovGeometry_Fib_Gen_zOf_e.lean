-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_zOf_e
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.zOf_e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:32.6291+00:00
-- url     : https://prove2.me/theorems/bc78c5fc-2e65-4fa0-9212-e59bff1cc8f7
-- title:
--   Gen: z Of e
-- statement:
--   The Gen construction uses the z Of e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStB.lean#L61-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStB.lean#L61-L73

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.zOf_e (hw : G.Good w) {ρ : ℂ} (hρ : G.P.eval₂ (deh w 0) ρ = 0) (k : Fin (D + 1)) :
    G.zOf w ρ (e k) = w k := by sorry
