-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_relabelRingEquiv_X_7a46ccc5629a
-- name    : P2M_GroundTheory_Heights__Heights_relabelRingEquiv_X_7a46ccc5629a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:58.045845+00:00
-- url     : https://prove2.me/theorems/c4fc3269-6cb5-4b91-8c0c-7a4de4306ded
-- title:
--   P2 M Ground Theory Heights  Heights relabel Ring Equiv X 7a46ccc5629a: P2 M Ground Theory Heights  Heights relabel Ring Equiv X 7a46ccc5629a
-- statement:
--   The P2 M Ground Theory Heights  Heights relabel Ring Equiv X 7a46ccc5629a construction uses the P2 M Ground Theory Heights  Heights relabel Ring Equiv X 7a46ccc5629a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L191-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L191-L194

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option linter.unusedSectionVars false
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))

theorem P2M_GroundTheory_Heights__Heights_relabelRingEquiv_X_7a46ccc5629a (k : K) (i : ι k) :
    relabelRingEquiv ε h (X ⟨k, i⟩) = X ⟨ε k, cast (h k) i⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«relabelRingEquiv_X» := P2M_GroundTheory_Heights__Heights_relabelRingEquiv_X_7a46ccc5629a
