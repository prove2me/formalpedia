-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_cell_3c1642189a4e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_cell_3c1642189a4e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:40.433923+00:00
-- url     : https://prove2.me/theorems/f46a5619-41bb-485e-95b7-fa616b6fd867
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ext cell 3c1642189a4e: P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ext cell 3c1642189a4e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ext cell 3c1642189a4e construction uses the P2 M Ground Theory Heights  Heights Kleiman KHComb Contract ext cell 3c1642189a4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L224-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean#L224-L227

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
variable {S : Type} [CommRing S]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_cell_3c1642189a4e (J : ∀ k, Finset (ι k)) (n : ℕ) (φ : CombC S J n) (I : CombCell ι J n) :
    ext J n φ I.1.1 = φ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHCombContract».«ext_cell» := P2M_GroundTheory_Heights__Heights_Kleiman_KHCombContract_ext_cell_3c1642189a4e
