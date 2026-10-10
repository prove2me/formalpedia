-- Prove2me | Theorems.Thm_QCQPTightness_MultTight_dual_certificate_19
-- name    : QCQPTightness.MultTight.dual_certificate_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:20.910273+00:00
-- url     : https://prove2.me/theorems/f750d1e3-1248-4d02-947a-6087e4720c02
-- title:
--   App. B, proof of Theorem 8, p. 35 — every (x̂, t̂) ∈ 𝒟_SDP ∩ H has Z ∈ 𝕊^n with (x̂, t̂, Z) satisfying (19)
-- statement:
--   Suppose Assumption 1 holds and the QCQP has an explicit representation $A_i = I_k\otimes\mathbb A_i$ ($i\in[\![0,m]\!]$) with symmetric $\mathbb A_i\in\mathbb S^n$, $N = kn$. Let $H=\{(x,t) : 2t = \mathrm{Opt}_{\mathrm{SDP}}\}$. Then for every $(\hat x,\hat t)\in\mathcal D_{\mathrm{SDP}}\cap H$ there is $Z\in\mathbb S^n$ such that
--
--   $$\begin{cases} q_0(\hat x)+\langle\mathbb A_0,Z\rangle = 2\hat t,\\ q_i(\hat x)+\langle\mathbb A_i,Z\rangle\le 0, & i\in[\![m_I]\!],\\ q_i(\hat x)+\langle\mathbb A_i,Z\rangle = 0, & i\in[\![m_I+1,m]\!],\\ Z\succeq 0.\end{cases}\tag{19}$$
--
--   This is the dual attainment step of the proof of Theorem 8: on $H$ the value $2\hat t$ equals $\sup_{\gamma\in\Gamma}q(\gamma,\hat x)$, and the dual of that maximization, written with the small matrices $\mathbb A_i$, attains its value.
--
--   **Formalization Note** The representation is an explicit hypothesis rather than the maximal multiplicity, which makes the statement apply to every representation. The standing assumption $m\ge 1$ is dropped (not needed).
-- source:
--   arXiv:1911.09195v3, App. B, proof of Theorem 8, p. 35, display (19)

import Mathlib
import Definitions.Def_QCQPTightness_MultTight_QCQP
import Definitions.Def_QCQPTightness_MultTight_Mult
import Definitions.Def_QCQPTightness_MultTight_Kron

namespace QCQPTightness.MultTight

open QCQP Matrix

/-- App. B, proof of Theorem 8 (arXiv:1911.09195v3, p. 35): under Assumption 1, for every
representation `A_i = I_k ⊗ 𝔸_i` and every `(x̂, t̂) ∈ 𝒟_SDP ∩ H`, the dual SDP attains its
value: some `Z ∈ 𝕊^n` makes `(x̂, t̂, Z)` satisfy (19). -/
theorem dual_certificate_19 {N m : ℕ} (P : QCQP N m) (h1 : P.Assumption1)
    {k n : ℕ} (h : k * n = N) (𝔸₀ : Matrix (Fin n) (Fin n) ℝ)
    (𝔸 : Fin m → Matrix (Fin n) (Fin n) ℝ) (hrep : P.IsKronRep h 𝔸₀ 𝔸)
    (p : (Fin N → ℝ) × ℝ) (hp : p ∈ P.DSDP ∩ P.hyperplaneH) :
    ∃ Z : Matrix (Fin n) (Fin n) ℝ, P.IsDualCert19 h 𝔸₀ 𝔸 p.1 p.2 Z := by sorry

end QCQPTightness.MultTight
