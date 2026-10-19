-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_finite_obstructions
-- name    : QAlgorithms.Papers.Independent.Information100.P62.finite_obstructions
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:45:42.143317+00:00
-- url     : https://prove2.me/theorems/5eca9066-98ff-41d1-b749-ec587bd2c120
-- title:
--   Lemma 4.10: finite minimal obstruction set
-- statement:
--   For a nonzero finite-dimensional algebra $A$, every minimal forbidden type $B\in F(A)$ satisfies
--   $$\ell(B)\le\ell(A)+1,$$
--   with equality exactly for $B\cong\mathbb C^{\ell(A)+1}$. The set $F(A)$ is finite, and every nonzero algebra $C$ satisfies $C\not\le A$ if and only if some $B\in F(A)$ embeds in $C$. This provides a finite obstruction test.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 36, Lemma 4.10: finite minimal obstruction set

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.36, 37, Lemma 4.10: finite minimal obstruction set. -/
theorem finite_obstructions (A : Shape) (hA : Valid A) :
    (∀ B ∈ forbidden A, lengthDim B ≤ lengthDim A + 1 ∧
      (lengthDim B = lengthDim A + 1 ↔ B = classical (lengthDim A + 1))) ∧
    (forbidden A).Finite ∧ ∀ C, Valid C → (¬ Embeds C A ↔ ∃ B ∈ forbidden A, Embeds B C) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
