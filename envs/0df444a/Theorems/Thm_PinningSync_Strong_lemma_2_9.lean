-- Prove2me | Theorems.Thm_PinningSync_Strong_lemma_2_9
-- name    : PinningSync.Strong.lemma_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:24:14.701953+00:00
-- url     : https://prove2.me/theorems/b0af42c8-17bb-4d89-8aaa-e2c62db7dfec
-- title:
--   Lemma 2.9, p. 1400 — a nonnegative matrix with constant row sums has ρ(A) = ‖A‖∞
-- statement:
--   Let $A$ be a real $N\times N$ matrix with all entries $A_{ij}\ge 0$, and suppose that all its row sums are equal to a common value $r$. Then its spectral radius equals its maximum absolute row sum:
--   $$
--   \rho(A)=\|A\|_\infty .
--   $$
--
--   In the proof of Lemma 2.11 it is applied to $G+lI_N$, whose row sums all equal $l$.
--
--   **Formalization Note.** $\rho(A)$ is the largest modulus of a complex root of the characteristic polynomial of $A$; $\|A\|_\infty=\max_i\sum_j|A_{ij}|$. For $N=0$ both sides are $0$.
-- source:
--   Yu, Chen, Lü, Kurths, Synchronization via pinning control on general complex networks, SIAM J. Control Optim. 51 (2013), p. 1400, Lemma 2.9

import Mathlib
import Definitions.Def_PinningSync_Strong_Setting

namespace PinningSync.Strong

theorem lemma_2_9 {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : ∀ i j, 0 ≤ A i j) (r : ℝ)
    (hrow : ∀ i, ∑ j, A i j = r) :
    specRad A = infNorm A := by sorry

end PinningSync.Strong
