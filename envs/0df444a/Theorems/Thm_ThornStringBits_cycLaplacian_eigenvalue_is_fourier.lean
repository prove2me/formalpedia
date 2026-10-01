-- Prove2me | Theorems.Thm_ThornStringBits_cycLaplacian_eigenvalue_is_fourier
-- name    : ThornStringBits.cycLaplacian_eigenvalue_is_fourier
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T01:42:16.022862+00:00
-- url     : https://prove2.me/theorems/f10d1548-ec7e-4e7c-8da7-1b2d4dbe172d
-- title:
--   Every eigenvalue of the cyclic Laplacian is some $4\sin^2(\pi k/M)$, $k<M$
-- statement:
--   Let $M\in\mathbb N$ and let $\mu\in\mathbb R$ be an eigenvalue of the cyclic Laplacian $L_M$ acting on $\mathbb R^M$. Then there is an integer $k$ with $0\le k<M$ such that
--   $$ \mu = 4\sin^2\!\Bigl(\frac{\pi k}{M}\Bigr). $$
--
--   Combined with the previous milestone, the eigenvalues of $L_M$ are exactly $\{4\sin^2(\pi k/M):0\le k<M\}$, i.e. the normal-mode frequencies of Thorn's harmonic discretized string are exactly $(2/\epsilon)\sin(\pi k/M)$.
-- source:
--   C. B. Thorn, *Reformulating String Theory with the 1/N Expansion*, arXiv:hep-th/9405069v1 (1994; talk at the First Int. A. D. Sakharov Conf., 1991), https://arxiv.org/abs/hep-th/9405069, pp. 4–5.

import Definitions.Def_ThornStringBits_Defs
import Mathlib

open Real Matrix

namespace ThornStringBits

theorem cycLaplacian_eigenvalue_is_fourier (M : ℕ) (μ : ℝ)
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' (cycLaplacian M)) μ) :
    ∃ k : ℕ, k < M ∧ μ = 4 * Real.sin (π * k / M) ^ 2 := by sorry

end ThornStringBits
