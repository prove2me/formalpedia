-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_substitution_comp_relation
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.substitution_comp_relation
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:32:07.380826+00:00
-- url     : https://prove2.me/theorems/c11922df-abcc-4926-89c2-87abd13e404d
-- title:
--   Data: substitution comp relation
-- statement:
--   The Data construction uses the substitution comp relation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SubstitutionVanishesOfRelation.lean#L38-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SubstitutionVanishesOfRelation.lean#L38-L75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZEqConstMulIrreduciblePow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstitutionSplitIrreducibleOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstitutionVanishesOfRelation
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.substitution_comp_relation (hd : d.AxH 𝒜) (c : ι) :
    (d.linearSubstitution c).comp (MvPolynomial.aeval (fun t : TVar d.D d.N =>
      (MvPolynomial.X (Sum.inr 0) * MvPolynomial.X (Sum.inl (t.1.succ, t.2)) -
        MvPolynomial.X (Sum.inr t.1.succ) * MvPolynomial.X (Sum.inl (0, t.2)) :
          MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K))) =
      ((d.pluckerSubstitution c).restrictScalars K).comp (d.relationEliminateColumn c) := by sorry
