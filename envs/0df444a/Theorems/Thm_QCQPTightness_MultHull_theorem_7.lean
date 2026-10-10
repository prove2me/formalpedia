-- Prove2me | Theorems.Thm_QCQPTightness_MultHull_theorem_7
-- name    : QCQPTightness.MultHull.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:21:54.448966+00:00
-- url     : https://prove2.me/theorems/3c5fdef4-e41e-4630-85a7-90ca9d23f49e
-- title:
--   Theorem 7, p. 29 — if the quadratic eigenvalue multiplicity satisfies k ≥ m + 2, then conv(𝒟) = 𝒟_SDP
-- statement:
--   Consider a QCQP (1) in $N$ variables with $m\ge1$ constraints, $q_i(x) = x^\top A_ix + 2b_i^\top x + c_i$, its epigraph $\mathcal D$ (2) and the projected epigraph $\mathcal D_{\mathrm{SDP}}$ (4) of its Shor SDP relaxation. Suppose Assumption 1 holds: the QCQP is feasible and some $\gamma^*\in\mathbb R^m$ with $\gamma^*_i\ge 0$ for $i\in[\![m_I]\!]$ has $A_0+\sum_i\gamma^*_iA_i\succ0$. If the quadratic eigenvalue multiplicity $k$ (the largest $k$ with $A_i = I_k\otimes\mathbb A_i$ for all $i\in[\![0,m]\!]$, Definition 3) satisfies $k\ge m+2$, then
--
--   $$\operatorname{conv}(\mathcal D) = \mathcal D_{\mathrm{SDP}} .$$
--
--   Unlike Theorems 1 and 2 of the paper, this result needs neither the polyhedrality of $\Gamma$ (Assumption 3) nor the attainment Assumption 2: enough block symmetry in the quadratic forms alone forces the Shor relaxation to describe the convex hull of the epigraph exactly.
--
--   **Formalization Note** Constraint indices are shifted to $\{0,\dots,m-1\}$, with the first $m_I$ being inequalities. $\operatorname{conv}$ is Mathlib's `convexHull` in $\mathbb R^N\times\mathbb R$. The multiplicity enters as `IsQuadEigMult k` (the largest admissible $k$), exactly as on the page; for $N = 0$ no such $k$ exists and the statement is vacuous, a degenerate case the paper does not consider.
-- source:
--   arXiv:1911.09195v3, Theorem 7, p. 29

import Mathlib
import Definitions.Def_QCQPTightness_MultHull_QCQP
import Definitions.Def_QCQPTightness_MultHull_Mult

namespace QCQPTightness.MultHull

open Matrix

theorem theorem_7 {N m : ℕ} (P : QCQP N m) (hm : 1 ≤ m) (h1 : P.Assumption1)
    (k : ℕ) (hk : P.IsQuadEigMult k) (hkm : m + 2 ≤ k) :
    convexHull ℝ P.D = P.DSDP := by sorry

end QCQPTightness.MultHull
