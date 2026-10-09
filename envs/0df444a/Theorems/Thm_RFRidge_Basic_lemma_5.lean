-- Prove2me | Theorems.Thm_RFRidge_Basic_lemma_5
-- name    : RFRidge.Basic.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:49:57.000894+00:00
-- url     : https://prove2.me/theorems/baea96a1-40f0-4320-9d0d-64c70d17aeb3
-- title:
--   Lemma 5, p. 22 — ‖LL_λ^{-1}Pf_ρ − Pf_ρ‖ ≤ Rλ^r under the source condition Pf_ρ = L^r g, 1/2 ≤ r ≤ 1
-- statement:
--   Let $L$ be a bounded positive operator on a Hilbert space, $L_\lambda=L+\lambda I$, and suppose the source condition (15) holds: $Pf_\rho=L^rg$ with $\tfrac12\le r\le1$ and $\|g\|\le R$. Then for every $\lambda>0$,
--   $$\big\|LL_\lambda^{-1}Pf_\rho-Pf_\rho\big\|\le R\lambda^r .$$
--
--   This bounds the approximation error (21), the last term of the excess-risk decomposition.
--
--   **Formalization Note** (a) The page's $L$ is the integral operator on $L^2(X,\rho_X)$; its proof uses only that $L$ is bounded, self-adjoint and positive, and the statement is posed for every such operator, with $h$ standing for $Pf_\rho$. (b) $r\le1$ is added: Eq. (15) alone allows $r>1$, but the proof needs $\|\lambda^{1-r}L_\lambda^{-(1-r)}\|\le1$, which holds for $r\le1$ (Assumption 6's range); for $r>1$ the bound fails ($L=I$, $h=g$: the left side is $\lambda\|g\|/(1+\lambda)>\|g\|\lambda^r$ for small $\lambda$). (c) $\|g\|\le R$ covers both $R=\|g\|$ (Eq. (15)) and $R=1\vee\|g\|$ (Assumption 6). (d) The space is complex and $LL_\lambda^{-1}$ is the functional calculus of $t\mapsto t/(t+\lambda)$; see Proposition 4.
-- source:
--   Rudi & Rosasco, arXiv:1602.04474v5, Lemma 5, p. 22; Eq. (15), p. 18; Assumption 6, p. 17

import Mathlib

namespace RFRidge.Basic

/-- Lemma 5, p. 22: for a positive bounded operator `L` on a Hilbert space, `P f_ρ = L^r g` (Eq. (15)) with
`1/2 ≤ r ≤ 1` and `‖g‖ ≤ R`, and every `λ > 0`, `‖L L_λ^{-1} P f_ρ − P f_ρ‖ ≤ R λ^r`, where
`L L_λ^{-1} = L (L + λI)^{-1}` is the functional calculus of `t ↦ t / (t + λ)`. The vector `h` stands for
`P f_ρ`. Posed on a complex Hilbert space. -/
theorem lemma_5 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (L : E →L[ℂ] E) (hL : 0 ≤ L) (r R : ℝ) (hr0 : 1 / 2 ≤ r) (hr1 : r ≤ 1)
    (g h : E) (hh : h = (L ^ r) g) (hg : ‖g‖ ≤ R) (lam : ℝ) (hlam : 0 < lam) :
    ‖(cfc (fun t : ℝ => t / (t + lam)) L) h - h‖ ≤ R * lam ^ r := by sorry

end RFRidge.Basic
