-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_sig_fprod
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.sig_fprod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:15:36.808804+00:00
-- url     : https://prove2.me/theorems/1fdffc66-250d-41f2-bad9-d2dca0ab21cb
-- title:
--   Data: sig fprod
-- statement:
--   The Data construction uses the sig fprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FprodNeZero.lean#L75-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FprodNeZero.lean#L75-L117

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UnitAtIntAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DePres
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AGFrameNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Hartogs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FprodNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.sig_fprod (E : Ideal (KTp K d.D d.N) → ℤ) (hE : {q | q ∈ d.HtOne ∧ E q ≠ 0}.Finite)
    (hg : ∀ q ∈ d.HtOne, E q ≠ 0 → ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous
      (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen q)) (d.gen q))
    (bb : Fin (d.D + 1)) (u : Kˣ) :
    sigF (K := K) (D := d.D) (N := d.N) bb u (∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) =
      algebraMap K (KTf K d.D d.N) (u : K) ^ (∑ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
        E q * ((if bb = 0 then 0 else d.dg (d.gen q) : ℕ) : ℤ)) *
      ∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q := by sorry
