-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_padicValNat_absNorm_eq_sum
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.padicValNat_absNorm_eq_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:04.028042+00:00
-- url     : https://prove2.me/theorems/a23db296-84f6-565a-91fd-f5d361d50dff
-- title:
--   Pf: padic Val Nat abs Norm eq sum
-- statement:
--   The Pf construction uses the padic Val Nat abs Norm eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/PadicValNatAbsNormEqZero.lean#L119-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/PadicValNatAbsNormEqZero.lean#L119-L181

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_DiffAtOddSt
import Definitions.Def_Lemmata_MiscLemmasK_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaL_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField UniqueFactorizationMonoid Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.padicValNat_absNorm_eq_sum (ℓ : ℕ) [Fact ℓ.Prime] {X : Ideal (𝓞 E)} (hX : X ≠ ⊥) :
    padicValNat ℓ (Ideal.absNorm X) = ∑ Q ∈ (normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).toFinset,
      (normalizedFactors X).count Q * padicValNat ℓ (Ideal.absNorm Q) := by sorry
