-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_ConjugateOfRoots_conj_of_roots
-- name    : UpperTheory.Reformulated.B.ConjugateOfRoots.conj_of_roots
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:12.997213+00:00
-- url     : https://prove2.me/theorems/66fbefa4-e431-4c2d-9b79-38bc4921a3b5
-- title:
--   Conjugate Of Roots: conj of roots
-- statement:
--   The Conjugate Of Roots construction uses the conj of roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ConjugateOfRoots.lean#L7-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ConjugateOfRoots.lean#L7-L37

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ConjugateOfRoots
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.ConjugateOfRoots

theorem UpperTheory.Reformulated.B.ConjugateOfRoots.conj_of_roots {K : Type} [Field K] {n : ℕ} (d : Fin n → K) (hd : Function.Injective d) (N D : GL (Fin n) K)
    (hD : (D : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d)
    (hN : ∀ i, (N : Matrix (Fin n) (Fin n) K).charpoly.IsRoot (d i)) : ∃ g : GL (Fin n) K, N = g * D * g⁻¹ := by sorry
