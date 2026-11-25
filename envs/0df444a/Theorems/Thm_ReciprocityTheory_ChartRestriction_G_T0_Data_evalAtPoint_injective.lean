-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_evalAtPoint_injective
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.evalAtPoint_injective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:36:39.170867+00:00
-- url     : https://prove2.me/theorems/f4748109-d7c4-4316-9a4c-60a99854230d
-- title:
--   Data: eval At Point injective
-- statement:
--   The Data construction uses the eval At Point injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SacSuccAbove.lean#L181-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SacSuccAbove.lean#L181-L215

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
variable (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) (pt : TVar d.D d.N → ℂ)
  (hpt : ∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 → eval₂ sg pt q ≠ 0)
include hd h hpt

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.evalAtPoint_injective (P : Ω c →+* ℂ) (hP : P ∈ d.ST c sg (fun i j => pt (i.succ, j))) :
    Function.Injective (d.evP c P pt) := by sorry
