-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sign_gt_862abbabeb9e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sign_gt_862abbabeb9e
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:33.746+00:00
-- url     : https://prove2.me/theorems/ae642631-3ad7-4a64-9866-b3015b17043b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sign gt 862abbabeb9e: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sign gt 862abbabeb9e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sign gt 862abbabeb9e construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract sign gt 862abbabeb9e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L62-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L62-L80

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sign_gt_862abbabeb9e (T : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (l : K) (i : ι l) (hkl : k < l)
    (hk0 : i₀ ∉ T k) (hkne : (T k).Nonempty) :
    KH.faceSign (ins k i₀ (rem T l i)) k i₀ = KH.faceSign (ins k i₀ T) k i₀ ∧
      KH.faceSign (ins k i₀ T) l i = - KH.faceSign T l i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«sign_gt» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_sign_gt_862abbabeb9e
