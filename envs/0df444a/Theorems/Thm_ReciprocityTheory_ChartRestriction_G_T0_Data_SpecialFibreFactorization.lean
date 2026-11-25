-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_SpecialFibreFactorization
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.SpecialFibreFactorization
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:04:25.6108+00:00
-- url     : https://prove2.me/theorems/5de340de-d1fa-410c-a1c0-3b530ef468e0
-- title:
--   Data: Special Fibre Factorization
-- statement:
--   The Data construction uses the Special Fibre Factorization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SpecialFibreFactorization.lean#L21-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SpecialFibreFactorization.lean#L21-L58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormGenericRatioSpec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstRowZeroFixOfDegreeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_X4v4RatioSpec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SpecialFibreFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.SpecialFibreFactorization (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c)
    (x : Fin (d.N + 1) → K) (hx : d.wx x c ≠ 0) :
    ∃ κ : K, κ ≠ 0 ∧
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
        (MvPolynomial.aeval (fun v : TVar d.D d.N =>
          if v.1 = 0 then MvPolynomial.C (x v.2) else MvPolynomial.X v) F) =
      algebraMap K (KTf K d.D d.N) κ *
        ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.wx x c) p := by sorry
