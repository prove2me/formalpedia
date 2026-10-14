-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_codeBounds
-- name    : QAlgorithms.GottesmanIntro.codeBounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T18:04:08.532166+00:00
-- url     : https://prove2.me/theorems/80e49801-dd1d-443f-9463-daf4ce5fa1c5
-- title:
--   Quantum Gilbert–Varshamov, quantum Hamming, and asymptotic rate bounds
-- statement:
--   An $[[n,k,d]]$ code is a subspace $C$ of $(\mathbb C^2)^{\otimes n}$ of dimension $2^k$ such that every operator $E$ acting on at most $d-1$ qubits satisfies $\langle\psi|E|\psi\rangle=c'(E)$ for all unit vectors $|\psi\rangle\in C$, with $c'(E)$ independent of $|\psi\rangle$ (eq. (34)); that is, $C$ has distance at least $d$. Put $t=\lfloor (d-1)/2\rfloor$. The code is nondegenerate if, for every unit vector $|\psi\rangle\in C$, the Gram matrix $\big(\langle\psi|P_a^\dagger P_b|\psi\rangle\big)_{a,b}$ over the phase-free Pauli operators $P_a$ of weight at most $t$ is nonsingular. Let $H(x)=-x\log_2x-(1-x)\log_2(1-x)$.
--
--   1. (Quantum Gilbert–Varshamov bound.) If $d\ge1$ and
--   $$
--   \Big(\sum_{j=0}^{d-1}3^j\binom nj\Big)2^k\le 2^n,
--   $$
--   then an $[[n,k,d]]$ code exists.
--   2. (Quantum Hamming bound.) Every nondegenerate $[[n,k,d]]$ code satisfies
--   $$
--   \Big(\sum_{j=0}^{t}3^j\binom nj\Big)2^k\le 2^n.
--   $$
--   3. (Asymptotic rates.) Let $0<p<1/2$ and $\varepsilon>0$. There is $N$ such that for every $n\ge N$:
--      - every nondegenerate $[[n,k,d]]$ code with $d\ge 2pn$ has $k/n\le 1-p\log_2 3-H(p)+\varepsilon$;
--      - if $1-2p\log_2 3-H(2p)>0$, there is a nondegenerate $[[n,k,d]]$ code with $d\ge 2pn$ and $k/n\ge 1-2p\log_2 3-H(2p)-\varepsilon$.
--
--   The first two bounds are counting arguments. The third gives the rate window, eq. (37), between which the best nondegenerate codes lie.
--
--   **Formalization Note** The source's 'distance $d$' is read as distance at least $d$, so existence is meaningful also for $k=0$. The hypothesis $d\ge1$ excludes $d=0$, where (36) is an empty sum and the claim would demand a $2^k$-dimensional code for every $k$. The asymptotic clause is read as an $\varepsilon$–$N$ statement. The lower rate bound is asserted only when it is positive.
-- source:
--   Daniel Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, 2009, v1, PDF p. 7, Theorem 4. https://arxiv.org/pdf/0904.2557v1

import Definitions.Def_QAlgorithms_Defs_FTCircuit
set_option autoImplicit false

namespace QAlgorithms.GottesmanIntro

open scoped Matrix

open QAlgorithms Stabilizer




/-- Gottesman intro p.7–8, Theorem 4. (1) Quantum Gilbert–Varshamov: if
`(∑_{j=0}^{d-1} 3^j C(n,j)) 2^k ≤ 2^n` (eq. (36)) and `d ≥ 1`, an `[[n, k, d]]` code exists.
(2) Quantum Hamming bound: every nondegenerate `[[n, k, d]]` code satisfies
`(∑_{j=0}^{t} 3^j C(n,j)) 2^k ≤ 2^n` (eq. (35)), `t = ⌊(d-1)/2⌋`. (3) Asymptotics (eq. (37)):
for fixed `p ∈ (0, 1/2)` and every `ε > 0`, for all large `n`, every nondegenerate `[[n, k, d]]`
code with `d ≥ 2pn` has `k/n ≤ 1 - p log₂ 3 - H(p) + ε`, and, when `1 - 2p log₂ 3 - H(2p) > 0`,
some nondegenerate `[[n, k, d]]` code with `d ≥ 2pn` has `k/n ≥ 1 - 2p log₂ 3 - H(2p) - ε`. -/
theorem codeBounds :
    (∀ n k d : ℕ, 1 ≤ d →
      (∑ j ∈ Finset.range d, 3 ^ j * n.choose j) * 2 ^ k ≤ 2 ^ n →
      ∃ C : Submodule ℂ (EuclideanSpace ℂ (Qubits n)), IsQCode n k d C) ∧
    (∀ (n k d : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))), IsQCode n k d C →
      IsNondegenerate C ((d - 1) / 2) →
      (∑ j ∈ Finset.range ((d - 1) / 2 + 1), 3 ^ j * n.choose j) * 2 ^ k ≤ 2 ^ n) ∧
    ∀ p : ℝ, 0 < p → p < 1 / 2 → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (∀ (k d : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))), IsQCode n k d C →
        IsNondegenerate C ((d - 1) / 2) → 2 * p * n ≤ d →
        (k : ℝ) / n ≤ 1 - p * Real.logb 2 3 - binEntropy2 p + ε) ∧
      (0 < 1 - 2 * p * Real.logb 2 3 - binEntropy2 (2 * p) →
        ∃ (k d : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))), IsQCode n k d C ∧
          IsNondegenerate C ((d - 1) / 2) ∧ 2 * p * n ≤ d ∧
          1 - 2 * p * Real.logb 2 3 - binEntropy2 (2 * p) - ε ≤ (k : ℝ) / n) := by
  sorry

end QAlgorithms.GottesmanIntro
