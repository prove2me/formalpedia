-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_w_eq_count
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.w_eq_count
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:28.854925+00:00
-- url     : https://prove2.me/theorems/113b1813-704a-44fd-b642-b8b4bb67acbe
-- title:
--   ERam: w eq count
-- statement:
--   The ERam construction uses the w eq count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamVal.lean#L175-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamVal.lean#L175-L256

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField UniqueFactorizationMonoid Formalism.L2.Pj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {k : Type} [Field k] [Algebra V k]
  [IsFractionRing V k]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.w_eq_count (ψ : E →+* k) (hψ : Function.Injective ψ) (hP0 : primeOf (V := V) ψ hψ ≠ ⊥) :
    ∃ π : 𝓞 E, π ≠ 0 ∧ ∀ (n : ℕ) (x : 𝓞 E), x ≠ 0 →
      (normalizedFactors (Ideal.span {x})).count (primeOf (V := V) ψ hψ) = n →
      vV V (ψ (x : E)) = n * vV V (ψ (π : E)) := by sorry
