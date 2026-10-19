-- Prove2me | Theorems.Thm_QAlgorithms_Childs_clockPathMatrix_eigenvalue_localization
-- name    : QAlgorithms.Childs.clockPathMatrix_eigenvalue_localization
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T20:32:56.118274+00:00
-- url     : https://prove2.me/theorems/b78cf922-5cf4-4977-af64-cc9ab37d7722
-- title:
--   Clock path: localization of the ground and first excited eigenvalues
-- statement:
--   Let $k\ge1$, $s\in[0,1]$, and let $E_0\le E_1$ be the two smallest eigenvalues, counted with multiplicity, of the real symmetric path matrix with top-left entry $s-1$, adjacent off-diagonal entries $-s$, and all other entries zero. Then
--   $$
--   E_0\le s-1,\qquad E_1\ge-2s,\qquad
--   E_0\le-2s\cos\frac{\pi}{k+2}.
--   $$
--   If $s\le(k+1)/(2k+3)$, also $E_0\le-2s$ and $E_1\ge-2s\cos(\pi/(k+1))$.
--
--   For $s>0$ and $\pi/(k+1)<\theta<2\pi/(k+1)$, the following test locates the first excited eigenvalue:
--   $$
--   \frac{1-s}{s}<\frac{\sin((k+2)\theta)}{\sin((k+1)\theta)}
--   \quad\Longrightarrow\quad E_1\ge-2s\cos\theta.
--   $$
--   These localization statements separate the finite path's spectral calculation from quantitative estimates on its gap.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, https://www.cs.umd.edu/~amchilds/qa/qa.pdf, proof of Lemma 33.1, PDF pp. 182–183 (printed pp. 174–175), equations (33.17)–(33.23) and the monotone Chebyshev-ratio discussion. The first two rough bounds are the endpoint Rayleigh bound and interlacing with the principal path submatrix.

import Definitions.Def_QAlgorithms_Defs_Hamiltonian
set_option autoImplicit false

theorem QAlgorithms.Childs.clockPathMatrix_eigenvalue_localization
    (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    let E₀ := QAlgorithms.ascEigenvalues (QAlgorithms.clockPathMatrix k s)
      ⟨0, by simp⟩
    let E₁ := QAlgorithms.ascEigenvalues (QAlgorithms.clockPathMatrix k s)
      ⟨1, by simpa using Nat.succ_lt_succ hk⟩
    E₀ ≤ s - 1 ∧ -2 * s ≤ E₁ ∧
    E₀ ≤ -2 * s * Real.cos (Real.pi / ((k : ℝ) + 2)) ∧
    (s ≤ ((k : ℝ) + 1) / (2 * (k : ℝ) + 3) →
      E₀ ≤ -2 * s ∧
      -2 * s * Real.cos (Real.pi / ((k : ℝ) + 1)) ≤ E₁) ∧
    (∀ θ ∈ Set.Ioo (Real.pi / ((k : ℝ) + 1)) (2 * Real.pi / ((k : ℝ) + 1)),
      0 < s → (1 - s) / s <
        Real.sin (((k : ℝ) + 2) * θ) / Real.sin (((k : ℝ) + 1) * θ) →
      -2 * s * Real.cos θ ≤ E₁) := by sorry
