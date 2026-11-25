-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_exists_section
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.exists_section
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:01:14.654798+00:00
-- url     : https://prove2.me/theorems/ff4075da-e154-47dd-9332-a27b013af80c
-- title:
--   Gen: exists section
-- statement:
--   The Gen construction uses the exists section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStB.lean#L420-L477
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStB.lean#L420-L477

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
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω}
  {e : Fin (D + 1) → ι} (G : Gen x e)

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.exists_section (hx0 : x (e 0) ≠ 0) {W : Set (Fin (D + 1) → ℂ)} (hWo : IsOpen W)
    (hgood : ∀ w ∈ W, G.Good w) {w : Fin (D + 1) → ℂ} (hw : w ∈ W) {z : ι → ℂ}
    (hz : z ∈ fib x e w) :
    ∃ (U : Set (Fin (D + 1) → ℂ)) (γ : (Fin (D + 1) → ℂ) → ι → ℂ),
      IsOpen U ∧ w ∈ U ∧ DifferentiableOn ℂ γ U ∧ γ w = z ∧ ∀ w' ∈ U, γ w' ∈ fib x e w' := by sorry
