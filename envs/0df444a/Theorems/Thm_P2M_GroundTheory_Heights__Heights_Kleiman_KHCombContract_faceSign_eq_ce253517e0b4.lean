-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_faceSign_eq_ce253517e0b4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_faceSign_eq_ce253517e0b4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:57.85444+00:00
-- url     : https://prove2.me/theorems/202b8f3e-98fa-4612-8963-ff216efd9553
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract face Sign eq ce253517e0b4: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract face Sign eq ce253517e0b4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract face Sign eq ce253517e0b4 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract face Sign eq ce253517e0b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L35-L38

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_faceSign_eq_ce253517e0b4 (T : ∀ k, Finset (ι k)) (l : K) (i : ι l) :
    KH.faceSign T l i = (-1) ^ ((T l).filter (· < i)).card *
      (-1) ^ ∑ x ∈ Finset.univ.filter (· < l), ((T x).card - 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«faceSign_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_faceSign_eq_ce253517e0b4
