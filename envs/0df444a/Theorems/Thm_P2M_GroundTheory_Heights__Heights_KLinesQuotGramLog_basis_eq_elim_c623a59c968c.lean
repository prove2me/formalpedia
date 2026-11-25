-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesQuotGramLog_basis_eq_elim_c623a59c968c
-- name    : P2M_GroundTheory_Heights__Heights_KLinesQuotGramLog_basis_eq_elim_c623a59c968c
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:08.466501+00:00
-- url     : https://prove2.me/theorems/7052e1bd-2559-43cf-afb0-0ad755def536
-- title:
--   P2 M Ground Theory Heights  Heights KLines Quot Gram Log basis eq elim c623a59c968c: P2 M Ground Theory Heights  Heights KLines Quot Gram Log basis eq elim c623a59c968c
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Quot Gram Log basis eq elim c623a59c968c construction uses the P2 M Ground Theory Heights  Heights KLines Quot Gram Log basis eq elim c623a59c968c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesQuotGramLog.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesQuotGramLog.lean#L12-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotGramLog
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
open Matrix
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.KLinesQuotGramLog

theorem P2M_GroundTheory_Heights__Heights_KLinesQuotGramLog_basis_eq_elim_c623a59c968c {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) (b : Fin m → Fin n → K) (τ : Fin k → Fin n)
    (hBl : ∀ i, B (Sum.inl i) = b i) (hBr : ∀ j, B (Sum.inr j) = Pi.single (τ j) 1) :
    (⇑B : Fin m ⊕ Fin k → Fin n → K) = Sum.elim b fun j => (Pi.single (τ j) 1 : Fin n → K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesQuotGramLog».«basis_eq_elim» := P2M_GroundTheory_Heights__Heights_KLinesQuotGramLog_basis_eq_elim_c623a59c968c
