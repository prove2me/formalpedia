-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_MirabolicColumnBlock_conj_diagonal
-- name    : UpperTheory.Reformulated.B.MirabolicColumnBlock.conj_diagonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:54.566265+00:00
-- url     : https://prove2.me/theorems/3bc0da9a-89fc-4d59-a43f-65d9afa4225e
-- title:
--   Mirabolic Column Block: conj diagonal
-- statement:
--   The Mirabolic Column Block construction uses the conj diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MirabolicColumnBlock.lean#L5-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MirabolicColumnBlock.lean#L5-L29

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MirabolicColumnBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.MirabolicColumnBlock

theorem UpperTheory.Reformulated.B.MirabolicColumnBlock.conj_diagonal {K : Type} [Field K] {n : ℕ} (d : Fin n → K) (hd : Function.Injective d)
    (M : Matrix (Fin n) (Fin n) K) (hM : M.charpoly = ∏ a, (Polynomial.X - Polynomial.C (d a))) :
    ∃ h : GL (Fin n) K, ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * h = Matrix.diagonal d := by sorry
