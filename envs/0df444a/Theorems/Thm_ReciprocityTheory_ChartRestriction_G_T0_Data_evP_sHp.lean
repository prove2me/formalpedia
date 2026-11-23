-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_evP_sHp
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.evP_sHp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:01:11.642017+00:00
-- url     : https://prove2.me/theorems/ac90e66e-795e-428f-83e0-1d22d4d1dbfb
-- title:
--   Data: ev P s Hp
-- statement:
--   The Data construction uses the ev P s Hp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SacSuccAbove.lean#L92-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SacSuccAbove.lean#L92-L126

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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.evP_sHp (c : ι) (sg : K →+* ℂ) (pt : TVar d.D d.N → ℂ) (hd : d.AxH 𝒜) (P : Ω c →+* ℂ)
    (hP : P ∈ PT (Ω := Ω c) sg)
    (heq : ∀ i : Fin d.D, ∑ j, pt (i.succ, j) * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) = 0)
    (q : MvPolynomial (TVar d.D d.N) K) : d.evP c P pt (d.sHp c q) = eval₂ sg pt q := by sorry
