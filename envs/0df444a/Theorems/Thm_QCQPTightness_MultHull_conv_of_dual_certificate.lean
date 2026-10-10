-- Prove2me | Theorems.Thm_QCQPTightness_MultHull_conv_of_dual_certificate
-- name    : QCQPTightness.MultHull.conv_of_dual_certificate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:23:31.341189+00:00
-- url     : https://prove2.me/theorems/5b497582-a1af-43a1-ba77-5f1255dc2fb7
-- title:
--   §6, proof of Theorem 7, pp. 29–30 — if k ≥ m + 2, every (x̂, t̂, Z) satisfying (17) has (x̂, t̂) ∈ conv(𝒟)
-- statement:
--   Let $N = kn$ with $k\ge m+2$, and let $A_i = I_k\otimes\mathbb A_i$ ($i\in[\![0,m]\!]$) be an explicit representation of the quadratic forms of a QCQP (1) with symmetric $\mathbb A_i\in\mathbb S^n$. Then for every $\hat x\in\mathbb R^N$, $\hat t\in\mathbb R$ and $Z\in\mathbb S^n$ such that $(\hat x,\hat t, Z)$ satisfies (17),
--
--   $$(\hat x,\hat t)\in\operatorname{conv}(\mathcal D),$$
--
--   where $\mathcal D = \{(x,t) : q_0(x)\le 2t,\ q_i(x)\le 0\ (i\in[\![m_I]\!]),\ q_i(x)=0\ (i\in[\![m_I+1,m]\!])\}$ is the epigraph (2).
--
--   In the paper this is proved by induction on $\operatorname{rank}(Z)$; together with the existence of a solution of (17) for every point of $\mathcal D_{\mathrm{SDP}}$, it gives $\mathcal D_{\mathrm{SDP}}\subseteq\operatorname{conv}(\mathcal D)$, the nontrivial inclusion of Theorem 7.
--
--   **Formalization Note** Assumption 1 and the standing assumption $m\ge1$ are not used by this claim and are dropped, which makes the statement stronger. The representation is an arbitrary explicit one.
-- source:
--   arXiv:1911.09195v3, §6, proof of Theorem 7, pp. 29–30, the claim proved by induction on rank(Z)

import Mathlib
import Definitions.Def_QCQPTightness_MultHull_QCQP
import Definitions.Def_QCQPTightness_MultHull_Mult
import Definitions.Def_QCQPTightness_MultHull_Kron

namespace QCQPTightness.MultHull

open Matrix

theorem conv_of_dual_certificate {N m k n : ℕ} (P : QCQP N m) (h : k * n = N)
    (𝔸₀ : Matrix (Fin n) (Fin n) ℝ) (𝔸 : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hrep : P.IsKronRep h 𝔸₀ 𝔸) (hkm : m + 2 ≤ k) :
    ∀ (x : Fin N → ℝ) (t : ℝ) (Z : Matrix (Fin n) (Fin n) ℝ),
      P.IsDualCert 𝔸₀ 𝔸 x t Z → (x, t) ∈ convexHull ℝ P.D := by sorry

end QCQPTightness.MultHull
