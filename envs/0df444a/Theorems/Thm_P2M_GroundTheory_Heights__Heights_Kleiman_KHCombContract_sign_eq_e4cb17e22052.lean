-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sign_eq_e4cb17e22052
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sign_eq_e4cb17e22052
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:28:38.198018+00:00
-- url     : https://prove2.me/theorems/a16c4cb2-b383-4e4f-a744-e524bc8889b1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sign eq e4cb17e22052: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sign eq e4cb17e22052
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sign eq e4cb17e22052 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sign eq e4cb17e22052 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L82-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L82-L108

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombContract
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
open GroundTheory.Heights₂.Heights.Kleiman.KHCombContract
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sign_eq_e4cb17e22052 (T : ∀ k, Finset (ι k)) (k : K) (i₀ i : ι k) (hi : i ∈ T k) (hk0 : i₀ ∉ T k) :
    KH.faceSign T k i * KH.faceSign (ins k i₀ (rem T k i)) k i₀ =
      - (KH.faceSign (ins k i₀ T) k i₀ * KH.faceSign (ins k i₀ T) k i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«sign_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sign_eq_e4cb17e22052
