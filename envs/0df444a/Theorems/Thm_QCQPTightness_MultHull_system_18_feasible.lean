-- Prove2me | Theorems.Thm_QCQPTightness_MultHull_system_18_feasible
-- name    : QCQPTightness.MultHull.system_18_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:23:41.524807+00:00
-- url     : https://prove2.me/theorems/fc7d0593-b68f-49f4-800d-f303b01c206b
-- title:
--   §6, proof of Theorem 7, p. 30 — if k ≥ m + 2, system (18) has a solution y ∈ 𝐒^{k−1}
-- statement:
--   Let $N = kn$ with $k\ge m+2$, let $\hat x\in\mathbb R^N$ and $z\in\mathbb R^n$, and let $(A_i, b_i)_{i=0}^m$ be the quadratic and linear data of a QCQP with $m$ constraints. Then the system in $y\in\mathbb R^k$
--
--   $$\begin{cases}\langle A_0\hat x + b_0,\ y\otimes z\rangle = 0\\ \langle A_i\hat x + b_i,\ y\otimes z\rangle = 0, & i\in[\![m]\!]\\ y\in\mathbf S^{k-1}\end{cases}\qquad(18)$$
--
--   is feasible, where $\mathbf S^{k-1}$ is the Euclidean unit sphere of $\mathbb R^k$ and $y\otimes z$ is the vector whose $j$-th block of $n$ entries is $y_jz$.
--
--   The first $m+1$ equations are homogeneous and linear in $y$; with $k\ge m+2$ unknowns they have a nonzero solution. The unit vector $y$ is the direction along which the proof of Theorem 7 splits a point of $\mathcal D_{\mathrm{SDP}}$ into two.
--
--   **Formalization Note** $y\in\mathbf S^{k-1}$ is written $y^\top y = 1$. No Kronecker structure of the $A_i$ is assumed: the claim is pure linear algebra in $y$.
-- source:
--   arXiv:1911.09195v3, §6, proof of Theorem 7, p. 30, display (18) and the claim that it is feasible

import Mathlib
import Definitions.Def_QCQPTightness_MultHull_QCQP
import Definitions.Def_QCQPTightness_MultHull_Mult
import Definitions.Def_QCQPTightness_MultHull_Kron

namespace QCQPTightness.MultHull

open Matrix

theorem system_18_feasible {N m k n : ℕ} (P : QCQP N m) (h : k * n = N) (hkm : m + 2 ≤ k)
    (x : Fin N → ℝ) (z : Fin n → ℝ) :
    ∃ y : Fin k → ℝ, y ⬝ᵥ y = 1 ∧
      (P.A₀ *ᵥ x + P.b₀) ⬝ᵥ kronVec h y z = 0 ∧
      ∀ i, (P.A i *ᵥ x + P.b i) ⬝ᵥ kronVec h y z = 0 := by sorry

end QCQPTightness.MultHull
