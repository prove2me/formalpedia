-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_derivation_restPolynomial_b9129232db91
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_derivation_restPolynomial_b9129232db91
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:49.302871+00:00
-- url     : https://prove2.me/theorems/83241389-e441-4d1b-a6c3-5b1ace27ee9b
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag derivation rest Polynomial b9129232db91: P2 M Ground Theory Heights  Heights Rest Terms Flag derivation rest Polynomial b9129232db91
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag derivation rest Polynomial b9129232db91 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag derivation rest Polynomial b9129232db91 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L181-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L181-L213

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
variable (f r a : ℕ) (c : SmallBlock)

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_derivation_restPolynomial_b9129232db91 (D : Derivation ℚ (RootRing f (r + a)) (RootRing f (r + a)))
    (α β : Fin f → ℚ) (hy : ∀ σ i, D (X (yIndex f r a c σ i)) = C (α σ))
    (hz : ∀ σ i, D (X (zIndex f r a c σ i)) = C (β σ)) :
    D (fibreClass f r a c) = 0 ∧
    D (restPolynomial f r a c) =
      C (((f * (r * a) + 1 : ℕ) : ℚ) * (c.sign * r * ∑ σ, α σ)) *
        (smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«derivation_restPolynomial» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_derivation_restPolynomial_b9129232db91
