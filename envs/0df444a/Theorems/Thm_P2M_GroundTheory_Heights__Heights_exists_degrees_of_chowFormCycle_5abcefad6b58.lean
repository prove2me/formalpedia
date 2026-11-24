-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_degrees_of_chowFormCycle_5abcefad6b58
-- name    : P2M_GroundTheory_Heights__Heights_exists_degrees_of_chowFormCycle_5abcefad6b58
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:44.651294+00:00
-- url     : https://prove2.me/theorems/d6f51db7-f815-4afd-aabc-654c8a337011
-- title:
--   P2 M Ground Theory Heights  Heights exists degrees of chow Form Cycle 5abcefad6b58: P2 M Ground Theory Heights  Heights exists degrees of chow Form Cycle 5abcefad6b58
-- statement:
--   The P2 M Ground Theory Heights  Heights exists degrees of chow Form Cycle 5abcefad6b58 construction uses the P2 M Ground Theory Heights  Heights exists degrees of chow Form Cycle 5abcefad6b58 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L224-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L224-L255

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {k n : ℕ} {F : Type} [Field F]

theorem P2M_GroundTheory_Heights__Heights_exists_degrees_of_chowFormCycle_5abcefad6b58 (hk : 0 < k) (Z : ProjCycle F n) (c : F)
    (g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin k × Fin n) F)
    (hg : ∀ W ∈ Z.support, IsChowForm W k (g W)) {δ : ℕ}
    (hf : IsMultiHomog δ (C c * ∏ W ∈ Z.support, g W ^ Z W)) (hf0 : C c * ∏ W ∈ Z.support, g W ^ Z W ≠ 0) :
    ∃ δW : Ideal (MvPolynomial (Fin n) F) → ℕ, (∀ W ∈ Z.support, IsMultiHomog (δW W) (g W)) ∧
      ∑ W ∈ Z.support, Z W * δW W = δ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_degrees_of_chowFormCycle» := P2M_GroundTheory_Heights__Heights_exists_degrees_of_chowFormCycle_5abcefad6b58
