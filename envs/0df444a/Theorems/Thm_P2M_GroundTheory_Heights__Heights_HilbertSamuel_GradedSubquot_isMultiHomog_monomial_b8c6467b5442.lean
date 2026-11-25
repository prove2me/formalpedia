-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_isMultiHomog_monomial_b8c6467b5442
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_isMultiHomog_monomial_b8c6467b5442
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:20.259196+00:00
-- url     : https://prove2.me/theorems/44b4ca10-f283-59b1-a5c2-dc2c9b6696ae
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot is Multi Homog monomial b8c6467b5442: P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot is Multi Homog monomial b8c646
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot is Multi Homog monomial b8c6467b5442 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot is Multi Homog monomial b8c6467b5442 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGradedSubquot.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGradedSubquot.lean#L61-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGradedSubquot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGradedSubquot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubquot
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_isMultiHomog_monomial_b8c6467b5442 (d : (Σ k, ι k) →₀ ℕ) (r : S) (a : K → ℕ)
    (hd : ∀ k, ∑ i, d ⟨k, i⟩ = a k) : IsMultiHomog (monomial d r : MRingOver S ι) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GradedSubquot».«isMultiHomog_monomial» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_isMultiHomog_monomial_b8c6467b5442
