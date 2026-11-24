-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_cml_perm
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.cml_perm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:44:27.332823+00:00
-- url     : https://prove2.me/theorems/ce366297-b807-4faa-98b6-026449c117ec
-- title:
--   Pullback Sections: cml perm
-- statement:
--   The Pullback Sections construction uses the cml perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L17-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L17-L60

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped ContDiff
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.cml_perm {l l' : List V} (p : l.Perm l') :
    ∀ (n : ℕ) (M : ContinuousMultilinearMap ℂ (fun _ : Fin n => V) ℂ),
      (∀ (v : Fin n → V) (σ : Equiv.Perm (Fin n)), M (v ∘ σ) = M v) →
      ∀ (h : l.length = n) (h' : l'.length = n),
        M (fun i => l.get (i.cast h.symm)) = M (fun i => l'.get (i.cast h'.symm)) := by sorry
