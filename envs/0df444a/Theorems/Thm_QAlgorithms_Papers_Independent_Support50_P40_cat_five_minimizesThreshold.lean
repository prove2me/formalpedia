-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P40_cat_five_minimizesThreshold
-- name    : QAlgorithms.Papers.Independent.Support50.P40.cat_five_minimizesThreshold
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:07:41.173204+00:00
-- url     : https://prove2.me/theorems/10112e60-d800-42cd-a40c-07cc3a94f4d8
-- title:
--   Five-qubit cats minimize the single-cat threshold
-- statement:
--   For the ordinary positive-length cat family, let $q_p(f)$ be its exact signed concatenation yield under independent depolarization, and define $\tau_p=\inf\{f\in[3/4,1]:q_p(f)>0\}$. Each defining set contains the noiseless point $1$; the case $p=1$ is ordinary hashing.
--
--   The prose and Table I assert
--
--   $$
--   \tau_5\le\tau_p\quad\text{for every integer }p\ge1,\qquad
--   \tau_5<\tau_1,\qquad
--   \tau_1<\tau_p\quad\text{for every integer }p\ge15.
--   $$
--
--   Thus block size five is a minimizer within the single-cat family and strictly improves hashing. The statement does not assert a unique minimizer, optimality over all stabilizer codes, or optimality over multiple concatenations. The printed finite thresholds are not definitions of these real infima.
-- source:
--   Quantum Channel Capacity of Very Noisy Channels, arXiv:quant-ph/9706061v3, PDF p. 19, Section V.B and Table I: p=5 minimizes the single-cat threshold

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P40

namespace QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer

open scoped ComplexConjugate Matrix

noncomputable section

/-- PDF p.19, Table I p.25: the five-qubit cat minimizes the threshold
among ALL positive single-cat block sizes, strictly improves hashing,
and every unlisted finite size p>=15 is worse than hashing. This is a non-strict minimizer;
no uniqueness or optimality among arbitrary codes/concatenations is claimed. -/
theorem cat_five_minimizesThreshold :
    (∀ m : ℕ, catThreshold 4 ≤ catThreshold m) ∧
    catThreshold 4 < catThreshold 0 ∧
    (∀ m : ℕ, 14 ≤ m → catThreshold 0 < catThreshold m) := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P40
