-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_normForm_map_eq_prod_2f88ffb29b65
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_normForm_map_eq_prod_2f88ffb29b65
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:25.943548+00:00
-- url     : https://prove2.me/theorems/e586e322-b643-49e1-bfc6-75442f6b707b
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible norm Form map eq prod 2f88ffb29b65: P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible norm Form map eq prod 2f88ffb2
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible norm Form map eq prod 2f88ffb29b65 construction uses the P2 M Ground Theory Heights  Heights Vertical Norm Form Irreducible norm Form map eq prod 2f88ffb29b65 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L98-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormFormIrreducible.lean#L98-L148

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
variable {E L K : Type*} [Field E] [Field L] [Field K] [Algebra E L] [Algebra E K] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_normForm_map_eq_prod_2f88ffb29b65 [FiniteDimensional E L] [Algebra.IsSeparable E L] [IsAlgClosed K]
    (x : Fin n → L) :
    (normForm (R := E) L x).map (algebraMap E K) = ∏ σ : L →ₐ[E] K, embForm σ x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«NormFormIrreducible».«normForm_map_eq_prod» := P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_normForm_map_eq_prod_2f88ffb29b65
