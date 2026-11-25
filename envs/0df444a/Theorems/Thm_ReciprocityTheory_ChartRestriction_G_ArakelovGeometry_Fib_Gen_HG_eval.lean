-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_HG_eval
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.HG_eval
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:00:12.161268+00:00
-- url     : https://prove2.me/theorems/d0f715d1-07a3-5ce8-94b6-1d7fd13b7c21
-- title:
--   Gen: HG eval
-- statement:
--   The Gen construction uses the HG eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStA.lean#L171-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStA.lean#L171-L189

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.HG_eval [DecidableEq ι] (G : Gen x e) {S : Type*} [Field S]
    (ψ : MvPolynomial (Fin (D + 1)) ℤ →+* S) (t : S) (hd : ψ G.dd ≠ 0) (F : MvPolynomial ι ℤ) :
    (G.HG F).eval₂ ψ t =
      ψ G.dd ^ F.totalDegree * MvPolynomial.eval₂ (Int.castRingHom S) (G.evQ ψ t) F := by sorry
