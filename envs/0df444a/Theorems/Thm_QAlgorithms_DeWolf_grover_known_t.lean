-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_grover_known_t
-- name    : QAlgorithms.DeWolf.grover_known_t
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:42:15.180765+00:00
-- url     : https://prove2.me/theorems/7f0aefa8-b4af-4c2a-b7b1-fea9982ed066
-- title:
--   Grover's algorithm with known t: P_k = sin²((2k+1)θ), and k ≈ π/(4θ) − 1/2 ≤ (π/4)√(N/t) iterations succeed with probability ≥ 1 − t/N
-- statement:
--   Let $n\ge 0$, $N=2^n$, and let $x\in\{0,1\}^N$ be an input with $t\ge 1$ solutions, where $t=|x|$ is the Hamming weight of $x$. Let $O_{x,\pm}|i\rangle=(-1)^{x_i}|i\rangle$ be the phase query, $R_0$ the reflection that fixes $|0^n\rangle$ and multiplies every other basis state by $-1$, and $G=H^{\otimes n}R_0H^{\otimes n}O_{x,\pm}$ the Grover iterate. Write
--
--   $$P_k=\sum_{i:\,x_i=1}\bigl|\langle i|G^kH^{\otimes n}|0^n\rangle\bigr|^2$$
--
--   for the probability that measuring after $k$ Grover iterates (hence $k$ queries) yields a solution, and put $\theta=\arcsin\sqrt{t/N}$.
--
--   1. For every $k\in\mathbb N$, $P_k=\sin^2((2k+1)\theta)$.
--   2. If $k\in\mathbb N$ is an integer closest to $\tilde k=\frac{\pi}{4\theta}-\frac12$, i.e. $|k-\tilde k|\le\frac12$, then
--
--   $$P_k\ge 1-\frac tN\qquad\text{and}\qquad k\le\frac{\pi}{4\theta}\le\frac\pi4\sqrt{\frac Nt}.$$
--
--   Since the number of iterations depends only on $N$ and $t$, this is a bounded-error search algorithm using $O(\sqrt{N/t})$ queries when $t$ is known; it is the quadratic speed-up of Grover search over classical $\Theta(N)$.
--
--   **Formalization Note** The excluded case $t=0$ would make $\theta=0$ and $\pi/(4\theta)$ undefined. The case $t=N$ is allowed ($\theta=\pi/2$, $k=0$). The source's informal proviso $t\ll N$ is not needed for the inequality and is not a hypothesis.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 67, §7.2. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Search
set_option autoImplicit false

namespace QAlgorithms.DeWolf

open QAlgorithms

/-- de Wolf §7.2, PDF pp.65–68 (unnumbered): Grover's algorithm with a known number of
solutions.

Let `N = 2^n`, `x ∈ {0,1}^N` with `t ≥ 1` solutions (`t` the Hamming weight of `x`), and
`θ = arcsin √(t/N)`. Grover's algorithm prepares `H^{⊗n}|0^n⟩`, applies the Grover iterate
`G = H^{⊗n} R_0 H^{⊗n} O_{x,±}` (one phase query each) `k` times and measures.
1. For every `k`, the probability of measuring a solution is `P_k = sin²((2k+1)θ)`.
2. If `k` is an integer closest to `k̃ = π/(4θ) − 1/2`, then `1 − P_k ≤ t/N` and the number of
   queries satisfies `k ≤ π/(4θ) ≤ (π/4)√(N/t)`. -/
theorem grover_known_t (n : ℕ) (x : Qubits n → Bool) (ht : 1 ≤ hammingWeight x) :
    (∀ k : ℕ, groverSuccessProb x k =
        Real.sin ((2 * k + 1) * groverAngle (hammingWeight x) (2 ^ n)) ^ 2) ∧
    ∀ k : ℕ, |(k : ℝ) - (Real.pi / (4 * groverAngle (hammingWeight x) (2 ^ n)) - 1 / 2)| ≤ 1 / 2 →
      1 - (hammingWeight x : ℝ) / ((2 ^ n : ℕ) : ℝ) ≤ groverSuccessProb x k ∧
      (k : ℝ) ≤ Real.pi / (4 * groverAngle (hammingWeight x) (2 ^ n)) ∧
      Real.pi / (4 * groverAngle (hammingWeight x) (2 ^ n)) ≤
        Real.pi / 4 * Real.sqrt (((2 ^ n : ℕ) : ℝ) / (hammingWeight x : ℝ)) := by
  sorry


end QAlgorithms.DeWolf
