-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_aeval_trv_set
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.aeval_trv_set
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:09:17.419896+00:00
-- url     : https://prove2.me/theorems/4dac0751-0f67-5d22-bb2a-6bee89646011
-- title:
--   Data: aeval trv set
-- statement:
--   The Data construction uses the aeval trv set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PowFirstVarDvdSubstitution.lean#L56-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PowFirstVarDvdSubstitution.lean#L56-L73

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RelationMapCommTransvection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PowFirstVarDvdSubstitution
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.aeval_trv_set (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (k : Fin (d.D + 1))
    (s : Finset (Fin (d.D + 1))) (hks : k ∉ s)
    {S : Type*} [CommRing S] [Algebra K S] (r : TVar d.D d.N → S) (b : Fin (d.D + 1) → S) :
    aeval (fun t => if t.1 ∈ s then r t + b t.1 * r (k, t.2) else r t) F0 = aeval r F0 := by sorry
