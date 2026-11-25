-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_altSum_eq_7363a236564f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_altSum_eq_7363a236564f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:57:36.25549+00:00
-- url     : https://prove2.me/theorems/6b9face3-52d7-4556-bc18-f688ce6c5ad1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity alt Sum eq 7363a236564f: P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity alt Sum eq 7363a236564f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity alt Sum eq 7363a236564f construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity alt Sum eq 7363a236564f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L18-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L18-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSubquotFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd
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
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotientAdditivity

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_altSum_eq_7363a236564f {k : Type u} [Field k] (A B C : ℕ → Type v)
    [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)] [∀ i, FiniteDimensional k (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)] [∀ i, FiniteDimensional k (B i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module k (C i)] [∀ i, FiniteDimensional k (C i)]
    (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i) (δ : ∀ i, C i →ₗ[k] A (i + 1))
    (h0 : Function.Injective (f 0)) (hfg : ∀ i, Function.Exact (f i) (g i))
    (hgδ : ∀ i, Function.Exact (g i) (δ i)) (hδf : ∀ i, Function.Exact (δ i) (f (i + 1))) (M : ℕ) :
    ∑ i ∈ Finset.range (M + 1), (-1 : ℤ) ^ i *
      ((Module.finrank k (A i) : ℤ) - Module.finrank k (B i) + Module.finrank k (C i)) =
      (-1 : ℤ) ^ M * Module.finrank k (LinearMap.range (δ M)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotientAdditivity».«altSum_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_altSum_eq_7363a236564f
