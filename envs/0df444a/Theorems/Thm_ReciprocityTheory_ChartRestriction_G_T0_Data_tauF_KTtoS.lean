-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_tauF_KTtoS
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.tauF_KTtoS
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:36:13.879259+00:00
-- url     : https://prove2.me/theorems/2a7ec2fc-a0e1-42e6-a83b-6c7ccc3d92ff
-- title:
--   Data: tau F KTto S
-- statement:
--   The Data construction uses the tau F KTto S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ScaleMultiHomogeneous.lean#L236-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ScaleMultiHomogeneous.lean#L236-L253

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (NumberField.RingOfIntegers K) (A c)]
variable (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.tauF_KTtoS (h : d.S1) (c : ι) (b : Fin (d.D + 1)) (hb : b ≠ 0) (u : Kˣ)
    (z : KTf K d.D d.N) :
    tauF (Ω := Ω c) b u (d.KTtoS h c z) = d.KTtoS h c (sigF b u z) := by sorry
