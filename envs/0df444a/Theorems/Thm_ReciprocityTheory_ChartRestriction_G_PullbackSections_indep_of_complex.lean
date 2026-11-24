-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_indep_of_complex
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.indep_of_complex
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:09:06.637564+00:00
-- url     : https://prove2.me/theorems/c216e674-1d7e-40b0-a4b2-c3e597e12480
-- title:
--   Pullback Sections: indep of complex
-- statement:
--   The Pullback Sections construction uses the indep of complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/IndepPts.lean#L22-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/IndepPts.lean#L22-L74

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_JInjCore
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DetAlg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_IndepPts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB
variable {K : Type} [Field K]
  (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
  (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
    (S →ₐ[K] T) → pts S → pts T → Prop)

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.indep_of_complex [Algebra K ℂ] (hWD : EvalWD pts mapR)
    (hBC : ∀ (p : TRing K) (φ : p.R →ₐ[K] ℂ) (y : pts p.R), ∃ z : pts ℂ, mapR φ y z)
    {n : ℕ} (b : Fin n → Rules pts) (hnat : ∀ i, IsNatural pts mapR (b i)) (hb : LinearIndependent K b)
    (c : Fin n → ℂ) (hc : ∀ z : pts ℂ, FromTest pts mapR z → ∑ i, c i * evalAt pts mapR (b i) z = 0) :
    c = 0 := by sorry
