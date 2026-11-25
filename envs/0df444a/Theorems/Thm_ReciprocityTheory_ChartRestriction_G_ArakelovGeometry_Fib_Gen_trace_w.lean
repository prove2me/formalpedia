-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_trace_w
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.trace_w
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:01:31.391441+00:00
-- url     : https://prove2.me/theorems/537da395-8d9f-4b87-a1d8-afbadaf99855
-- title:
--   Gen: trace w
-- statement:
--   The Gen construction uses the trace w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStC.lean#L172-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStC.lean#L172-L197

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
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
variable [DecidableEq ι] (G : Gen x e)

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.trace_w {w : Fin (D + 1) → ℂ} (hw : G.Good w) (Tr : Ω → Ω)
    (hTr : ∀ H, Tr (H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) = deh (x ∘ e) 0 (G.TrP H))
    (hsc : ∀ (m : MvPolynomial (Fin (D + 1)) ℤ) (F : MvPolynomial ι ℤ),
      Tr (deh (x ∘ e) 0 m * deh x (e 0) F) = deh (x ∘ e) 0 m * Tr (deh x (e 0) F))
    {f : MvPolynomial ι ℤ} {g : MvPolynomial (Fin (D + 1)) ℤ}
    (h : deh (x ∘ e) 0 g = Tr (deh x (e 0) f)) :
    deh w 0 g = ((G.P.map (deh w 0)).roots.map fun ρ => deh (G.zOf w ρ) (e 0) f).sum := by sorry
