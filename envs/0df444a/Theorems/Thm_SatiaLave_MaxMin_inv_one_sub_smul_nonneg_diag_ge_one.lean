-- Prove2me | Theorems.Thm_SatiaLave_MaxMin_inv_one_sub_smul_nonneg_diag_ge_one
-- name    : SatiaLave.MaxMin.inv_one_sub_smul_nonneg_diag_ge_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:37:54.606877+00:00
-- url     : https://prove2.me/theorems/d319a10b-cfbb-4f4c-929c-1fd0dc130564
-- title:
--   Proof of Proposition 5 — $[I-\beta P]^{-1}$ is nonnegative with diagonal at least 1
-- statement:
--   Let $P$ be an $N\times N$ stochastic matrix (nonnegative entries, every row summing to $1$) and let $0\le\beta<1$. Then $I-\beta P$ is invertible, and its inverse satisfies
--   $$\big([I-\beta P]^{-1}\big)_{ij}\ge 0\quad\text{for all } i,j,\qquad \big([I-\beta P]^{-1}\big)_{ii}\ge 1\quad\text{for all } i.$$
--
--   This is the matrix fact behind the improvement arguments in the proofs of Propositions 3, 4 and 5: a nonnegative vector $\eta$ with one positive entry is mapped by $[I-\beta P]^{-1}$ to a nonnegative vector with a positive entry.
--
--   **Formalization Note.** Invertibility is stated explicitly (`IsUnit`), since Lean's matrix inverse is $0$ for a singular matrix.
-- source:
--   Satia and Lave, Markovian Decision Processes with Uncertain Transition Probabilities, Operations Research 21(3), 1973, p. 732, Proof of Proposition 5

import Mathlib

namespace SatiaLave.MaxMin

/-- Proof of Proposition 5, p. 732: for a stochastic matrix `P` and a discount factor
`0 ≤ β < 1`, the matrix `I − βP` is invertible, its inverse has nonnegative entries, and every
diagonal entry of the inverse is at least `1`. -/
theorem inv_one_sub_smul_nonneg_diag_ge_one {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (hP_nonneg : ∀ i j, 0 ≤ P i j) (hP_sum : ∀ i, ∑ j, P i j = 1)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    IsUnit (1 - β • P) ∧ (∀ i j, 0 ≤ (1 - β • P)⁻¹ i j) ∧ ∀ i, 1 ≤ (1 - β • P)⁻¹ i i := by sorry

end SatiaLave.MaxMin
