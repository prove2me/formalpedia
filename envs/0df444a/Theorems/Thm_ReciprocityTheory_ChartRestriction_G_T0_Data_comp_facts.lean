-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_comp_facts
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.comp_facts
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:21:15.591236+00:00
-- url     : https://prove2.me/theorems/7e5552f4-e9d4-4174-93dc-a3159691a471
-- title:
--   Data: comp facts
-- statement:
--   The Data construction uses the comp facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAE.lean#L206-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAE.lean#L206-L263

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.comp_facts (hd : d.AxH 𝒜) (h : d.S1) (la : HeightOneSpectrum (𝓞 K)) (c : ι) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    letI : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := d.algOp h la c
    letI := algOpKT (K := K) d.D d.N la
    IsFractionRing (Op d.D d.N la) (KTf K d.D d.N) ∧
      IsScalarTower (Op d.D d.N la) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) ∧
      FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) ∧
      Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) ∧
      IsDedekindDomain (integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N)) ∧
      IsFractionRing (integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N)) (OmS (Ω c) d.D d.N) := by sorry
