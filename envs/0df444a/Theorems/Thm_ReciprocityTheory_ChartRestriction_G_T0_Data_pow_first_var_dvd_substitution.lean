-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_pow_first_var_dvd_substitution
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.pow_first_var_dvd_substitution
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:10:39.668052+00:00
-- url     : https://prove2.me/theorems/2d5d65b3-fd37-43f1-a34e-41edd732f5d4
-- title:
--   Data: pow first var dvd substitution
-- statement:
--   The Data construction uses the pow first var dvd substitution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PowFirstVarDvdSubstitution.lean#L75-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PowFirstVarDvdSubstitution.lean#L75-L135

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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.pow_first_var_dvd_substitution (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (d0 : ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F0) :
    (X (Sum.inr 0) : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) ^ (d.D * d0) ∣
      bilinearSubstitution F0 := by sorry
