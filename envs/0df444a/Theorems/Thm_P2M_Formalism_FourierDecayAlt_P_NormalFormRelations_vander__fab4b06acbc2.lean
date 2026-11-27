-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_NormalFormRelations_vander__fab4b06acbc2
-- name    : P2M_Formalism_FourierDecayAlt_P_NormalFormRelations_vander__fab4b06acbc2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:04:59.642423+00:00
-- url     : https://prove2.me/theorems/1905cfb2-806e-5414-b7ff-7a6d7d06d49f
-- title:
--   P2 M Formalism Fourier Decay Alt P Normal Form Relations vander  fab4b06acbc2: P2 M Formalism Fourier Decay Alt P Normal Form Relations vander  fab4b06acbc2
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Normal Form Relations vander  fab4b06acbc2 construction uses the P2 M Formalism Fourier Decay Alt P Normal Form Relations vander  fab4b06acbc2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/JacobiDiagonalBounds/Vander.lean#L5-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/JacobiDiagonalBounds/Vander.lean#L5-L27

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_JacobiDiagonalBounds_Vander
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NormalFormRelations

theorem P2M_Formalism_FourierDecayAlt_P_NormalFormRelations_vander__fab4b06acbc2 (Q : ℕ) : ∃ lam : Fin (Q + 1) → Fin (Q + 1) → ℂ, ∀ (E : Type) [AddCommGroup E] [Module ℂ E]
    (a : Fin (Q + 1) → E) (q : Fin (Q + 1)),
    a q = ∑ s : Fin (Q + 1), lam q s • ∑ j : Fin (Q + 1), (((s : ℕ) : ℂ) ^ (j : ℕ)) • a j := by sorry

alias «Formalism».«FourierDecayAlt».«P».«NormalFormRelations».«vander'» := P2M_Formalism_FourierDecayAlt_P_NormalFormRelations_vander__fab4b06acbc2
