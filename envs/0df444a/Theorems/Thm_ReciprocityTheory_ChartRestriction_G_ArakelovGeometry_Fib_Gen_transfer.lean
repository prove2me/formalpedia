-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_transfer
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.transfer
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:11:21.685091+00:00
-- url     : https://prove2.me/theorems/31b55930-7dad-438e-ae5e-8fcc8397af7c
-- title:
--   Gen: transfer
-- statement:
--   The Gen construction uses the transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStA.lean#L202-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStA.lean#L202-L214

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ}
variable {x : ι → Ω} {e : Fin (D + 1) → ι}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.transfer [DecidableEq ι] (G : Gen x e) (w : Fin (D + 1) → ℂ)
    (hker : ∀ m, deh (x ∘ e) 0 m = 0 → deh w 0 m = 0) (hdw : deh w 0 G.dd ≠ 0)
    {ρ : ℂ} (hρ : G.P.eval₂ (deh w 0) ρ = 0) {F : MvPolynomial ι ℤ}
    {H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)}
    (h : deh x (e 0) F = H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) (G.evQ (deh w 0) ρ) F = H.eval₂ (deh w 0) ρ := by sorry
