-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_mk_monomial_eq_1fcfa5cefa4b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_mk_monomial_eq_1fcfa5cefa4b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:29:01.795491+00:00
-- url     : https://prove2.me/theorems/5b7495c9-940a-4594-b5a4-2b62eb991878
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp mk monomial eq 1fcfa5cefa4b: P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp mk monomial eq 1fcfa5cefa4b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp mk monomial eq 1fcfa5cefa4b construction uses the P2 M Ground Theory Heights  Heights Kleiman KHFree Decomp mk monomial eq 1fcfa5cefa4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeDecomp.lean#L53-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHFreeDecomp.lean#L53-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeDecompSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHFreeDecomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.KHFreeDecomp
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_mk_monomial_eq_1fcfa5cefa4b (I : ∀ k, Finset (ι k)) (u v : (Σ k, ι k) →₀ ℕ) (hu : ∀ q ∈ u.support, q.2 ∈ I q.1)
    (ht : (monomial u (1 : S) : MRingOver S ι) ∈ KH.cellMon S I) :
    LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (monomial v 1)) ⟨monomial u 1, ht⟩ =
      monoFrac S I (fun q => (v q : ℤ) - u q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHFreeDecomp».«mk_monomial_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_mk_monomial_eq_1fcfa5cefa4b
