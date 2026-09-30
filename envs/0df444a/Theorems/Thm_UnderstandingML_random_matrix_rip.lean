-- Prove2me | Theorems.Thm_UnderstandingML_random_matrix_rip
-- name    : UnderstandingML.random_matrix_rip
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:27:30.480836+00:00
-- url     : https://prove2.me/theorems/751f499d-d74f-4ade-ab3f-8aebf2243310
-- title:
--   Theorem 23.9 (constants as proved): for orthonormal U, ε, δ ∈ (0,1), 1 ≤ s ≤ d and n ≥ 216 s log(72d/(δε))/ε², a random N(0,1/n) matrix W has WU (ε,s)-RIP w.p. ≥ 1 − δ
-- statement:
--   **Theorem 23.9.** Let $U$ be an arbitrary fixed $d \times d$ orthonormal matrix, let $\epsilon, \delta$ be scalars in $(0,1)$, let $s$ be an integer in $[d]$, and let $n$ be an integer that satisfies $n \ge 100\,s\log(40d/(\delta\epsilon))/\epsilon^2$. Let $W \in \mathbb{R}^{n \times d}$ be a matrix s.t. each element of $W$ is distributed normally with zero mean and variance of $1/n$. Then, with probability of at least $1 - \delta$ over the choice of $W$, the matrix $WU$ is $(\epsilon, s)$-RIP.
--
--   Formally, with the constants the book's proof gives: $n \ge 216\,s\log(72d/(\delta\epsilon))/\epsilon^2$ (Lemma 23.12 at $\epsilon/3$ and $\delta/d^s$, then a union bound over the $\le d^s$ index sets of size $s$). The stated constants $100$ and $40$ are not reached by that argument.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §23.3 p. 333, Theorem 23.9, proved on p. 337 from Lemma 23.12 and a union bound (Baraniuk, Davenport, DeVore and Wakin 2008)

import Definitions.Def_UnderstandingML_DimReduction

open MeasureTheory ProbabilityTheory

namespace UnderstandingML

/-- **Theorem 23.9** (p. 333), with the constants its proof gives. Let `U` be an arbitrary fixed
`d × d` orthonormal matrix, let `ε, δ ∈ (0, 1)`, let `s ∈ [d]`, and let `n` be an integer with
`n ≥ 216 s log(72 d/(δε))/ε²`. Let `W ∈ ℝ^{n×d}` be a matrix whose elements are independently
`N(0, 1/n)`. Then, with probability of at least `1 − δ` over the choice of `W`, the matrix `WU`
is `(ε, s)`-RIP. (The book states `n ≥ 100 s log(40d/(δε))/ε²`; the proof, Lemma 23.12 with
`ε/3` and a union bound over the `≤ d^s` index sets, gives the constants used here.) -/
theorem random_matrix_rip {d : ℕ} (U : Matrix (Fin d) (Fin d) ℝ) (hU : U.transpose * U = 1)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1) (s : ℕ) (hs : 1 ≤ s)
    (hsd : s ≤ d) (n : ℕ) (hn : 216 * s * Real.log (72 * d / (δ * ε)) / ε ^ 2 ≤ n) :
    gaussianMatrixLaw n d (n : NNReal)⁻¹ {W | ¬ IsRIP ε s (Matrix.of W * U)} ≤
      ENNReal.ofReal δ := by sorry

end UnderstandingML
