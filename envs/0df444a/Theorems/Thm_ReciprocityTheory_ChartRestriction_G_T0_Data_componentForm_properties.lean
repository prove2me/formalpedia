-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_componentForm_properties
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.componentForm_properties
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T04:41:50.446257+00:00
-- url     : https://prove2.me/theorems/a23a2761-18eb-5163-908a-01aebaaf8fef
-- title:
--   Data: component Form properties
-- statement:
--   The Data construction uses the component Form properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ComponentFormProperties.lean#L20-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ComponentFormProperties.lean#L20-L34

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DegreeSumIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SpecialFibreFactorization
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ComponentFormProperties
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_DegreeSumIdentity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_SpecialFibreFactorization

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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.componentForm_properties (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∃ F : KTp K d.D d.N, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c ∧ F ≠ 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) F ∧
      (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nPMM h c (d.w (d.jc c) c) p * (d.dg (d.gen p) : ℤ)) = d.delc c ∧
      ∀ x : Fin (d.N + 1) → K, d.wx x c ≠ 0 → ∃ κ : K, κ ≠ 0 ∧
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
          (MvPolynomial.aeval (fun v : TVar d.D d.N =>
            if v.1 = 0 then MvPolynomial.C (x v.2) else MvPolynomial.X v) F) =
        algebraMap K (KTf K d.D d.N) κ *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.wx x c) p := by sorry
