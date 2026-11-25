-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_exists_gen
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.exists_gen
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:02:24.583186+00:00
-- url     : https://prove2.me/theorems/1a585845-51b1-4213-9c64-33b92d32c165
-- title:
--   Fib: exists gen
-- statement:
--   The Fib construction uses the exists gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStE.lean#L18-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStE.lean#L18-L177

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.exists_gen (x : ι → Ω) (e : Fin (D + 1) → ι) (h : IsProjFrame x e) :
    ∃ G : Gen x e, G.P.natDegree = projDeg x e ∧
      (∀ H, fnTrace x e (H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) =
        deh (x ∘ e) 0 (G.TrP H)) ∧
      (∀ m F, fnTrace x e (deh (x ∘ e) 0 m * deh x (e 0) F) =
        deh (x ∘ e) 0 m * fnTrace x e (deh x (e 0) F)) := by sorry
