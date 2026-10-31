-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_twoSidedNormTraceCertificate
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.twoSidedNormTraceCertificate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:01:04.461509+00:00
-- url     : https://prove2.me/theorems/4e5c2b75-ea9f-4839-bd9c-8844ce2c0d31
-- title:
--   Exact two-sided norm and trace certificates with attainment
-- statement:
--   Let $n\ge1$, let $H$ be Hermitian and traceless, and fix a nonzero real time $\tau$. Put $U=e^{-i\tau H}$, $N=2^n$, and, for local special-unitary factors $K,L$, define $D(K,L)=\|KUL-U^\dagger\|_F^2$ and $f(K,L)=-\operatorname{Re}\operatorname{tr}(KULU)$. Then
--
--   $$D(K,L)=2N+2f(K,L),\qquad KUL=U^\dagger\ \Longleftrightarrow\ \|KUL-U^\dagger\|_F=0\ \Longleftrightarrow\ D(K,L)=0\ \Longleftrightarrow\ f(K,L)/N=-1.$$
--
--   There exists an attained global minimizing pair $(K_*,L_*)$, and some local pair inverts $U$ exactly if and only if $D(K_*,L_*)=0$. These criteria include trivial and conjugation cases, so they do not by themselves establish exclusive type-II membership. No gradient-search convergence is asserted.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 2, (4), (80)–(81): exact two-sided norm and trace certificate

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- (4),(80)–(81), PDF pp.2,14–15: exact two-sided inversion, including
trivial and conjugation cases. The objective is minimized with value -N,
N=2^n. The compact minimum ranges over all local pairs and is attained;
it does not certify exclusive type-II membership or numerical convergence. -/
theorem twoSidedNormTraceCertificate {n : ℕ} (hn : 0 < n)
    (H : Op (QAlgorithms.Qubits n)) (hH : IsHamiltonian H) (tau : ℝ) (htau : tau ≠ 0) :
    let U := evolution H tau
    (∀ K L : LocalSU n,
      twoSidedDistanceSq U K L = 2 * (2 : ℝ) ^ n + 2 * twoSidedObjective U K L) ∧
    (∀ K L : LocalSU n,
      (localMatrix K * U * localMatrix L = U.conjTranspose ↔
        QAlgorithms.frobNorm (localMatrix K * U * localMatrix L - U.conjTranspose) = 0) ∧
      (localMatrix K * U * localMatrix L = U.conjTranspose ↔
        twoSidedDistanceSq U K L = 0) ∧
      (localMatrix K * U * localMatrix L = U.conjTranspose ↔
        twoSidedObjective U K L / (2 : ℝ) ^ n = -1)) ∧
    (∃ Kmin Lmin : LocalSU n,
      (∀ K L : LocalSU n, twoSidedDistanceSq U Kmin Lmin ≤ twoSidedDistanceSq U K L) ∧
      ((∃ K L : LocalSU n, localMatrix K * U * localMatrix L = U.conjTranspose) ↔
        twoSidedDistanceSq U Kmin Lmin = 0)) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
