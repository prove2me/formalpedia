-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_irreducible_of_totalDegree_le_one_dc5ad9495e50
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_irreducible_of_totalDegree_le_one_dc5ad9495e50
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:43:30.223902+00:00
-- url     : https://prove2.me/theorems/10524b61-389b-5cff-9551-2ed2cf9adb95
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible irreducible of total Degree le one dc5ad9495e50: P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible irreducible of to
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible irreducible of total Degree le one dc5ad9495e50 construction uses the P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible irreducible of total Degree le one dc5ad9495e50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L162-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L162-L176

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial TensorProduct Matrix
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
variable {K : Type*} [Field K] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_irreducible_of_totalDegree_le_one_dc5ad9495e50 {ℓ : MvPolynomial (Fin n) K} (h1 : ℓ.totalDegree ≤ 1)
    (hc : ∀ r, ℓ ≠ C r) : Irreducible ℓ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«NormFormIrreducible».«irreducible_of_totalDegree_le_one» := P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_irreducible_of_totalDegree_le_one_dc5ad9495e50
