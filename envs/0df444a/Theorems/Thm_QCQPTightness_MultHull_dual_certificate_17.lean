-- Prove2me | Theorems.Thm_QCQPTightness_MultHull_dual_certificate_17
-- name    : QCQPTightness.MultHull.dual_certificate_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:51.542122+00:00
-- url     : https://prove2.me/theorems/3fb0f886-29d0-4dbf-a5c4-a6c05a34ddcf
-- title:
--   §6, proof of Theorem 7, p. 29 — every (x̂, t̂) ∈ 𝒟_SDP has Z ∈ 𝕊^n with (x̂, t̂, Z) satisfying (17)
-- statement:
--   Suppose Assumption 1 holds, and let $A_i = I_k\otimes\mathbb A_i$ ($i\in[\![0,m]\!]$) be an explicit representation of the quadratic forms with symmetric $\mathbb A_i\in\mathbb S^n$, $N = kn$. If $(\hat x,\hat t)\in\mathcal D_{\mathrm{SDP}}$, then there exists $Z\in\mathbb S^n$ such that
--
--   $$\begin{cases} q_0(\hat x) + \langle\mathbb A_0, Z\rangle \le 2\hat t\\ q_i(\hat x) + \langle\mathbb A_i, Z\rangle\le 0, & i\in[\![m_I]\!]\\ q_i(\hat x) + \langle\mathbb A_i, Z\rangle = 0, & i\in[\![m_I+1,m]\!]\\ Z\succeq 0.\end{cases}\qquad(17)$$
--
--   In the paper this is the dual attainment step: $2\hat t$ bounds $\sup\{q(\gamma,\hat x) : \mathbb A(\gamma)\succeq0,\ \gamma_i\ge0\ \forall i\in[\![m_I]\!]\}$, and Assumption 1 gives strong conic duality for this program with an attained dual optimum $Z$. It converts membership in the $N$-dimensional relaxation into an $n\times n$ certificate on which the rank induction of Theorem 7 runs.
--
--   **Formalization Note** Constraint indices are shifted to $\{0,\dots,m-1\}$. The representation is an arbitrary explicit one, which makes the statement at least as strong as for the largest $k$. The standing assumption $m\ge1$ is not needed and is dropped.
-- source:
--   arXiv:1911.09195v3, §6, proof of Theorem 7, p. 29, display (17)

import Mathlib
import Definitions.Def_QCQPTightness_MultHull_QCQP
import Definitions.Def_QCQPTightness_MultHull_Mult
import Definitions.Def_QCQPTightness_MultHull_Kron

namespace QCQPTightness.MultHull

open Matrix

theorem dual_certificate_17 {N m k n : ℕ} (P : QCQP N m) (h1 : P.Assumption1)
    (h : k * n = N) (𝔸₀ : Matrix (Fin n) (Fin n) ℝ) (𝔸 : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hrep : P.IsKronRep h 𝔸₀ 𝔸) (p : (Fin N → ℝ) × ℝ) (hp : p ∈ P.DSDP) :
    ∃ Z : Matrix (Fin n) (Fin n) ℝ, P.IsDualCert 𝔸₀ 𝔸 p.1 p.2 Z := by sorry

end QCQPTightness.MultHull
