-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_classical_quantum_side_system
-- name    : QAlgorithms.Papers.Independent.Information100.P62.classical_quantum_side_system
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T21:55:31.854605+00:00
-- url     : https://prove2.me/theorems/5dde0f75-537a-4f9c-9d70-a68212a244fb
-- title:
--   Lemma 5.1: classical channel with noiseless quantum side system
-- statement:
--   Let $N$ be a stochastic matrix, $\Phi_N$ its associated quantum channel, and $\alpha$ the independence number of its confusability graph. For every integer $d\ge1$,
--   $$M_d(\mathbb C)^{\oplus\alpha}\text{ is maximal in }\mathcal T(\Phi_N\otimes{\rm id}_d).$$
--   This is a maximality assertion; it does not assert domination.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 44, Lemma 5.1: classical channel with noiseless quantum side system

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.44, 45, Lemma 5.1: classical channel with noiseless quantum side system. -/
theorem classical_quantum_side_system [Nonempty I] [Nonempty O]
    (N : Matrix O I ℝ) (hN : Stochastic N) (d : ℕ) (hd : 1 ≤ d) :
    Maximal (tensorChannel (classicalChannel N) (id : Superop (Fin d) (Fin d)))
      (equalBlocks d (independence N)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
