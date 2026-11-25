-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_fnTrace_coe
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.fnTrace_coe
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:01:53.713872+00:00
-- url     : https://prove2.me/theorems/173f2298-e78f-5359-a237-fbd0062deb57
-- title:
--   Fib: fn Trace coe
-- statement:
--   The Fib construction uses the fn Trace coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStE.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStE.lean#L11-L16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStE
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module IntermediateField
variable {Ω : Type*} [Field Ω] [CharZero Ω] {ι : Type} [Fintype ι] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.fnTrace_coe (x : ι → Ω) (e : Fin (D + 1) → ι) (s : Lx x e) :
    fnTrace x e (s : Ω) =
      ((Algebra.trace (fnField (x ∘ e)) (Lx x e) s : fnField (x ∘ e)) : Ω) := by sorry
