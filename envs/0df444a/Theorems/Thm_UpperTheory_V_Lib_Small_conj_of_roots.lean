-- Prove2me | Theorems.Thm_UpperTheory_V_Lib_Small_conj_of_roots
-- name    : UpperTheory.V.Lib.Small.conj_of_roots
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:41:07.051367+00:00
-- url     : https://prove2.me/theorems/1f37af07-6a73-429a-a98d-6d94f708b83d
-- title:
--   Small: conj of roots
-- statement:
--   The Small construction uses the conj of roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/IntegralityNearIdentity/ExistsContDiffEventuallyEq.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/IntegralityNearIdentity/ExistsContDiffEventuallyEq.lean#L10-L13

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_IntegralityNearIdentity_EqOneOfNear
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ConjugateOfRoots
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WeightedSumBis
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_IntegralityNearIdentity_ExistsContDiffEventuallyEq
import Theorems.Thm_UpperTheory_Reformulated_B_ConjugateOfRoots_conj_of_roots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open UpperTheory UpperTheory.V UpperTheory.V.Lib UpperTheory.V.Lib.Small

theorem UpperTheory.V.Lib.Small.conj_of_roots {K : Type} [Field K] {n : ℕ} (d : Fin n → K) (hd : Function.Injective d) (N D : GL (Fin n) K)
    (hD : (D : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d)
    (hN : ∀ i, (N : Matrix (Fin n) (Fin n) K).charpoly.IsRoot (d i)) : ∃ g : GL (Fin n) K, N = g * D * g⁻¹ := by sorry
