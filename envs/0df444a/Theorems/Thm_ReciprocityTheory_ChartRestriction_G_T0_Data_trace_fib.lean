-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_trace_fib
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.trace_fib
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:36:09.33219+00:00
-- url     : https://prove2.me/theorems/69917d05-4106-50bc-8aef-bbe3a0b5f298
-- title:
--   Data: trace fib
-- statement:
--   The Data construction uses the trace fib property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TraceFib.lean#L19-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TraceFib.lean#L19-L39

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPtsB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TraceFib
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.trace_fib (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ)
    (y : Fin (d.N + 1 + d.D) → ℂ)
    (hpt : ∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 →
      eval₂ sg (NPB.gpt (fun q => t q.1 q.2) y) q ≠ 0) (g : Ω c) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    tauPev sg _ hpt (Algebra.trace (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
        (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g)) =
      ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t), P g := by sorry
