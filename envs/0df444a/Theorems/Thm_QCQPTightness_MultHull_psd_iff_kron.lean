-- Prove2me | Theorems.Thm_QCQPTightness_MultHull_psd_iff_kron
-- name    : QCQPTightness.MultHull.psd_iff_kron
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:41.708833+00:00
-- url     : https://prove2.me/theorems/8a8852d0-da65-42cc-9f3b-ec11451a0d28
-- title:
--   §6, proof of Theorem 7, p. 29 — A(γ) ⪰ 0 if and only if 𝔸(γ) ⪰ 0
-- statement:
--   Let $N = kn$ with $k\ge 1$, and suppose the QCQP's quadratic forms are $A_i = I_k\otimes\mathbb A_i$ with symmetric $\mathbb A_i\in\mathbb S^n$ for every $i\in[\![0,m]\!]$. Then for every $\gamma\in\mathbb R^m$,
--
--   $$A(\gamma) = A_0 + \sum_{i=1}^m\gamma_iA_i \succeq 0 \iff \mathbb A(\gamma) = \mathbb A_0 + \sum_{i=1}^m\gamma_i\mathbb A_i\succeq 0 .$$
--
--   This lets the dual problem $\sup_{\gamma\in\Gamma}q(\gamma,\hat x)$ be rewritten with the $n\times n$ constraint $\mathbb A(\gamma)\succeq0$ in place of the $N\times N$ one, which is the program to which the proof of Theorem 7 applies conic duality.
--
--   **Formalization Note** The hypothesis $k\ge 1$ is the paper's observation that the multiplicity is always at least $1$ (p. 11); for $k=0$ the matrix $A(\gamma)$ is empty and the equivalence fails. The representation $(\mathbb A_i)$ is explicit and arbitrary, not necessarily the one of the largest $k$.
-- source:
--   arXiv:1911.09195v3, §6, proof of Theorem 7, p. 29, "The second line follows as A(γ) ⪰ 0 if and only if 𝔸(γ) ⪰ 0"

import Mathlib
import Definitions.Def_QCQPTightness_MultHull_QCQP
import Definitions.Def_QCQPTightness_MultHull_Mult
import Definitions.Def_QCQPTightness_MultHull_Kron

namespace QCQPTightness.MultHull

open Matrix

theorem psd_iff_kron {N m k n : ℕ} (P : QCQP N m) (h : k * n = N) (hk : 0 < k)
    (𝔸₀ : Matrix (Fin n) (Fin n) ℝ) (𝔸 : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hrep : P.IsKronRep h 𝔸₀ 𝔸) (γ : Fin m → ℝ) :
    (P.Aγ γ).PosSemidef ↔ (kronAγ 𝔸₀ 𝔸 γ).PosSemidef := by sorry

end QCQPTightness.MultHull
