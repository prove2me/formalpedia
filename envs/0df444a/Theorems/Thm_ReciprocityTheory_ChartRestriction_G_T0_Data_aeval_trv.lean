-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_aeval_trv
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.aeval_trv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:49:25.246849+00:00
-- url     : https://prove2.me/theorems/ac414d37-2c54-4004-afe3-f8fac8005cbc
-- title:
--   Data: aeval trv
-- statement:
--   The Data construction uses the aeval trv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RelationMapCommTransvection.lean#L137-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RelationMapCommTransvection.lean#L137-L155

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZEqConstMulIrreduciblePow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RelationMapCommTransvection
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.aeval_trv (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (i k : Fin (d.D + 1)) (hik : i ≠ k)
    {S : Type*} [CommRing S] [Algebra K S] (r : TVar d.D d.N → S) (b : S) :
    aeval (fun t => if t.1 = i then r t + b * r (k, t.2) else r t) F0 = aeval r F0 := by sorry
