-- Prove2me | Theorems.Thm_QAlgorithms_Childs_szegedyWalk_spectrum
-- name    : QAlgorithms.Childs.szegedyWalk_spectrum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:37:02.531968+00:00
-- url     : https://prove2.me/theorems/520aab30-fc63-467a-a510-a2e5bd650a1a
-- title:
--   Spectrum of the Szegedy quantum walk
-- statement:
--   Let $P$ be an $N \times N$ stochastic matrix: $P_{kj} \ge 0$ is the probability of a transition to $k$ from $j$, and $\sum_{k=1}^N P_{kj} = 1$ for every $j$. On $\mathbb C^N \otimes \mathbb C^N$ define the states $|\psi_j\rangle = \sum_{k} \sqrt{P_{kj}}\,|j,k\rangle$, the projection $\Pi = \sum_j |\psi_j\rangle\langle\psi_j|$, the swap $S = \sum_{j,k} |j,k\rangle\langle k,j|$, and the quantum walk $U = S(2\Pi - 1)$. Let $D$ be the real symmetric $N\times N$ matrix with entries $D_{jk} = \sqrt{P_{jk}P_{kj}}$.
--
--   **Theorem.**
--
--   1. Every eigenvalue $\mu$ of $U$ satisfies $\mu \in \{1, -1\}$ or
--   $$
--   \mu = \lambda \pm i\sqrt{1-\lambda^2} \quad \text{for some eigenvalue } \lambda \text{ of } D.
--   $$
--   2. Conversely, for every eigenvalue $\lambda$ of $D$, both $\lambda + i\sqrt{1-\lambda^2}$ and $\lambda - i\sqrt{1-\lambda^2}$ are eigenvalues of $U$.
--
--   Since $|\lambda| \le 1$, these are the points $e^{\pm i \arccos \lambda}$ of the unit circle. The theorem relates the phases of the quantum walk to the spectrum of the classical chain, and underlies the quadratic speedup of quantum-walk search (the phase gap $\arccos\lambda$ versus the classical gap $1-\lambda$).
--
--   **Formalization Note** The values $\pm 1$ are stated as possible eigenvalues only: for $N = 1$, $P = (1)$, the walk is $U = (1)$, which has no eigenvalue $-1$. Eigenvalues of $U$ are taken over $\mathbb C$ and those of $D$ over $\mathbb R$; the form $\lambda \pm i\sqrt{1-\lambda^2}$ is used, which equals $e^{\pm i\arccos\lambda}$ on $[-1,1]$.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 91, Theorem 18.1. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Walk
set_option autoImplicit false

namespace QAlgorithms.Childs

/-- **Childs, Theorem 18.1** (PDF p. 91, proof pp. 91–92; definitions §18.2, p. 90). Fix an
`N × N` stochastic matrix `P`, and let `D` be the `N × N` matrix with entries
`D_jk = √(P_jk P_kj)` (`discriminant P`). Then the eigenvalues of the discrete-time quantum walk
`U = S(2Π − 1)` corresponding to `P` (`szegedyWalk P`) are `±1` and `λ ± i√(1 − λ²)`
(`= e^{± i arccos λ}`), where `λ` ranges over the eigenvalues of `D`.

Standing conventions of §18.2 (p. 90): `P_kj` is the probability of a transition to `k` from `j`,
and stochastic means nonnegative entries with `∑_k P_kj = 1` for every `j` (`IsColumnStochastic`);
`|ψ_j⟩ = ∑_k √P_kj |j, k⟩` (`szegedyState`), `Π = ∑_j |ψ_j⟩⟨ψ_j|` (`szegedyProj`),
`S = ∑_{j,k} |j, k⟩⟨k, j|` (`swapOp`), `U = S(2Π − 1)` (`szegedyWalk`).

The statement is read as two clauses: (1) every eigenvalue of `U` is `1`, `−1`, or
`λ ± i√(1 − λ²)` for an eigenvalue `λ` of `D`; (2) for every eigenvalue `λ` of `D`, both
`λ + i√(1 − λ²)` and `λ − i√(1 − λ²)` are eigenvalues of `U` (the proof's eigenvectors
`|λ̃⟩ − μ S|λ̃⟩`). The values `±1` are a containment only: for `N = 1`, `P = (1)`, `U = (1)` has
no eigenvalue `−1`. -/
theorem szegedyWalk_spectrum {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ)
    (hP : IsColumnStochastic P) :
    (∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (szegedyWalk P)) μ →
      μ = 1 ∨ μ = -1 ∨
        ∃ l : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (discriminant P)) l ∧
          (μ = (l : ℂ) + Complex.I * (Real.sqrt (1 - l ^ 2) : ℂ) ∨
            μ = (l : ℂ) - Complex.I * (Real.sqrt (1 - l ^ 2) : ℂ))) ∧
    (∀ l : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (discriminant P)) l →
      Module.End.HasEigenvalue (Matrix.toLin' (szegedyWalk P))
          ((l : ℂ) + Complex.I * (Real.sqrt (1 - l ^ 2) : ℂ)) ∧
        Module.End.HasEigenvalue (Matrix.toLin' (szegedyWalk P))
          ((l : ℂ) - Complex.I * (Real.sqrt (1 - l ^ 2) : ℂ))) := by
  sorry


end QAlgorithms.Childs
