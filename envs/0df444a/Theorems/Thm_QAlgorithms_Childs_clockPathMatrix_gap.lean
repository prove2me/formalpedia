-- Prove2me | Theorems.Thm_QAlgorithms_Childs_clockPathMatrix_gap
-- name    : QAlgorithms.Childs.clockPathMatrix_gap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:42:23.631576+00:00
-- url     : https://prove2.me/theorems/68c06452-9f1c-4869-8fab-a4dafba8bac0
-- title:
--   Ω(1/k²) spectral gap of the adiabatic clock Hamiltonian on the computational subspace
-- statement:
--   Let $k \ge 0$ be the number of gates of a quantum circuit and let $s \in [0,1]$. In the adiabatic simulation of the circuit, the interpolated Hamiltonian $H(s) = (1-s)H_B + sH_C$ leaves invariant the $(k+1)$-dimensional computational subspace spanned by the history states $|\psi_0\rangle, \dots, |\psi_k\rangle$, and on it acts, by $\langle\psi_j|H_B|\psi_{j'}\rangle = -\delta_{j,j'}\delta_{j,0}$ and $\langle\psi_j|H_C|\psi_{j'}\rangle = -(\delta_{j,j'+1}+\delta_{j,j'-1})$, as the real symmetric $(k+1)\times(k+1)$ matrix
--
--   $$A_k(s) = \begin{pmatrix} s-1 & -s & 0 & \cdots & 0 \\ -s & 0 & -s & \ddots & \vdots \\ 0 & -s & 0 & \ddots & 0 \\ \vdots & \ddots & \ddots & \ddots & -s \\ 0 & \cdots & 0 & -s & 0 \end{pmatrix},$$
--
--   whose $(0,0)$ entry is $s-1$, whose first off-diagonal entries are $-s$, and whose other entries vanish. Let $\lambda_0(s) \le \lambda_1(s) \le \cdots \le \lambda_k(s)$ be its eigenvalues, counted with multiplicity, and $\Delta_k(s) = \lambda_1(s) - \lambda_0(s)$ the gap between the smallest and the second smallest.
--
--   **Lemma.** The gap is $\Omega(1/k^2)$ uniformly in $s \in [0,1]$: there are a constant $c > 0$ and a threshold $k_0$ such that
--
--   $$\Delta_k(s) \ge \frac{c}{k^2} \qquad \text{for all } k \ge k_0 \text{ and all } s \in [0,1].$$
--
--   This bound on the minimum gap along the whole interpolation path is what makes an adiabatic evolution time $T = \mathrm{poly}(k)$ sufficient, and hence shows that adiabatic quantum computation can efficiently simulate the circuit model.
--
--   **Formalization Note** The matrix is the shared definition `clockPathMatrix k s` on $\mathrm{Fin}(k+1)$; the gap is `spectralGap`, the second smallest minus the smallest eigenvalue of the Hermitian matrix with multiplicity (so a degenerate ground level would give gap $0$). The constants $c$ and $k_0$ are quantified before $k$ and $s$.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 182, Lemma 33.1. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Hamiltonian
set_option autoImplicit false

namespace QAlgorithms.Childs

/-- Childs, Lemma 33.1 (PDF p. 182; matrix (33.16) on PDF p. 181): the gap between the smallest
and second smallest eigenvalues of the matrix (33.16) for `s ∈ [0, 1]` is `Ω(1/k²)`. The
constant `c > 0` and the threshold `k₀` are chosen before `k` and are uniform over
`s ∈ [0, 1]`. -/
theorem clockPathMatrix_gap :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ s ∈ Set.Icc (0 : ℝ) 1,
      c / (k : ℝ) ^ 2 ≤ spectralGap (clockPathMatrix k s) := by
  sorry

end QAlgorithms.Childs
