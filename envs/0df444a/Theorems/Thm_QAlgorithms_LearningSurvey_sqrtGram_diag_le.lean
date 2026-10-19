-- Prove2me | Theorems.Thm_QAlgorithms_LearningSurvey_sqrtGram_diag_le
-- name    : QAlgorithms.LearningSurvey.sqrtGram_diag_le
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:55:35.457875+00:00
-- url     : https://prove2.me/theorems/00383329-bafe-4da2-b701-531f305f7822
-- title:
--   Diagonal of the square root of an XOR-invariant Gram matrix (corrected: with the factor 2^{-k/2})
-- statement:
--   This is the spectral estimate behind the pretty-good-measurement lower bounds for quantum PAC and agnostic learning, stated with the decay factor that the source's application needs.
--
--   Let $m\ge 10$, $\beta\in(0,1]$ and let $T$ be a natural number with $1\le T\le m/(e^3\beta)$. Define $f:\{0,1\}^m\to\mathbb R$ by $f(w)=(1-\beta|w|/m)^T$, where $|w|$ is the Hamming weight. Let $k\le m$ and let $M\in\mathbb F_2^{m\times k}$ have rank $k$. Let $A$ be the $2^k\times 2^k$ real matrix $A(z,y)=f(M(z\oplus y))$, where $z\oplus y$ is addition in $\mathbb F_2^k$ and $M(z\oplus y)$ is the matrix-vector product over $\mathbb F_2$. The matrix $A$ is positive semidefinite; write $\sqrt A$ for its positive semidefinite square root.
--
--   There is an absolute constant $K>0$ such that for all such $m,k,\beta,T,M$ and every $z\in\{0,1\}^k$,
--
--   $$
--   \sqrt{A}(z,z)\ \le\ 2^{-k/2}\, e^{K\left(T\beta^2/m+\sqrt{Tm\beta}\right)} .
--   $$
--
--   Because the pretty-good-measurement success probability of the ensemble with Gram matrix $G=A/2^k$ is $\sum_z\sqrt G(z,z)^2=\sqrt A(z,z)^2$, this bound gives the exponentially small success probability used in the proofs of Theorems 4.12 and 4.15.
--
--   **Formalization Note** The source prints the bound without the factor $2^{-k/2}$. In that form it always holds trivially, since $\sqrt A(z,z)\le 1$. The factor is the decay that holds for every $k\le m$, and it cannot be improved (at $T=1$ and $\beta\to 0$, $\sqrt A(z,z)\to 2^{-k/2}$). $\sqrt A(z,z)$ is the $(z,z)$ entry of the square-root matrix, not the square root of the entry.
-- source:
--   Srinivasan Arunachalam and Ronald de Wolf, A Survey of Quantum Learning Theory, 2017, v3, PDF p. 13, Theorem 4.13. https://arxiv.org/pdf/1701.06806v3

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.LearningSurvey

open MeasureTheory QAlgorithms.Learning


/-- Corrected statement. survey p.13, Theorem 4.13 ([AW17, Theorem 17]). Printed: for `m ≥ 10`,
`f(w) = (1 − β|w|/m)^T` with `β ∈ (0, 1]`, `T ∈ [1, m/(e³β)]`, `k ≤ m`, `M ∈ F₂^{m×k}` of rank `k`
and `A(z, y) = (f ∘ M)(z ⊕ y)`, one has `√A(z, z) ≤ e^{O(Tβ²/m + √(Tmβ))}` for all `z`.

Changed: the bound carries the factor `2^{−k/2}`, i.e.
`√A(z, z) ≤ 2^{−k/2} · e^{K(Tβ²/m + √(Tmβ))}` with an absolute `K > 0`.

Why: as printed the bound is contentless. For integer `T`, `f ∘ M` has nonnegative Fourier
coefficients, so `A` is positive semidefinite with `A(z, z) = f(0) = 1`, and `√A(z, z) ≤ 1` always.
The source's own use (p.14, p.15: `P_pgm = Σ_z √G(z,z)² ≤ e^{O(Tε²/d + √(Tdε)) − d − Tε}`, with
`G = A/2^k`, so `P_pgm = √A(z,z)²`) needs a decaying factor that the printed statement drops
(trap 30). The decay that holds for every `k ≤ m` is `2^{−k/2}`. It cannot be `k`-independent
(at `k = 0`, `√A = 1`), and its rate is tight (at `T = 1`, `β → 0`, `√A(z,z) → 2^{−k/2}`). With
the proof's `k ≥ d/4` it gives the source's `e^{−Ω(d)}`.

`T` is a natural number (the number of copies in both applications), so `√A` is the positive
semidefinite square root (`psdSqrt`); `√A(z, z)` is the `(z, z)` entry of that root. -/
theorem sqrtGram_diag_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (m k : ℕ) (β : ℝ) (T : ℕ) (M : Matrix (Fin m) (Fin k) (ZMod 2))
      (z : Fin k → ZMod 2), 10 ≤ m → k ≤ m → 0 < β → β ≤ 1 → 1 ≤ T →
      (T : ℝ) ≤ (m : ℝ) / (Real.exp 3 * β) → M.rank = k →
      psdSqrt (xorConvMatrix fun x => weightPowFun m β T (M.mulVec x)) z z ≤
        (Real.sqrt 2)⁻¹ ^ k *
          Real.exp (K * ((T : ℝ) * β ^ 2 / (m : ℝ) + Real.sqrt ((T : ℝ) * (m : ℝ) * β))) := by sorry



end QAlgorithms.LearningSurvey
