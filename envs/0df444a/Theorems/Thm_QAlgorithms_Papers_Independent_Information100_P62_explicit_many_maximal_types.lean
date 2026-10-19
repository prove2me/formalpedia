-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_explicit_many_maximal_types
-- name    : QAlgorithms.Papers.Independent.Information100.P62.explicit_many_maximal_types
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T21:58:51.845635+00:00
-- url     : https://prove2.me/theorems/c166efe7-8cd7-48fe-86f2-872717b6656b
-- title:
--   Proposition 5.5: explicit exponentially and doubly exponentially many maximal types
-- statement:
--   For the explicit channels $\Phi$ of Example 4.3 and $\Psi=\Delta_2\otimes\Phi$, let $s_n(q)$ be the sum of $2^{|x|}$ over the first $q$ Boolean strings in increasing Hamming weight. For $n\ge1$ and $1\le q\le2^n$,
--   $$B_{n,q}=M_q(\mathbb C)\oplus\mathbb C^{3^n-s_n(q)}\in\max\mathcal T(\Phi^{\otimes n}).$$
--   Hence $w_n(\Phi)\ge2^n$. For every nonnegative multiplicity vector $(N_q)$ with $\sum_qN_q=2^n$, the type $\bigoplus_qB_{n,q}^{\oplus N_q}$ is maximal transmittable through $\Psi^{\otimes n}$, and $w_n(\Psi)\ge\binom{2^{n+1}-1}{2^n-1}\ge2^{2^n-1}$. This includes every allowed vector and the sharper count proved on p.55.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 48, Proposition 5.5: explicit exponentially and doubly exponentially many maximal types

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.48, 49, 53, 54, 55, Proposition 5.5: explicit exponentially and doubly exponentially many maximal types. -/
theorem explicit_many_maximal_types (n : ℕ) (hn : 1 ≤ n) :
    (∀ q, 1 ≤ q → q ≤ 2 ^ n → Maximal (tensorPower example43 n) (widthType n q)) ∧
    2 ^ n ≤ width example43 n ∧
    (∀ N : Fin (2 ^ n) → ℕ, (∑ q, N q) = 2 ^ n →
      Maximal (tensorPower selectorChannel n) (selectorType n N)) ∧
    Nat.choose (2 ^ (n + 1) - 1) (2 ^ n - 1) ≤ width selectorChannel n ∧
    2 ^ (2 ^ n - 1) ≤ width selectorChannel n := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
