-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P58_noFeedbackTestingConverse
-- name    : QAlgorithms.Papers.Independent.Information100.P58.noFeedbackTestingConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:14:29.634326+00:00
-- url     : https://prove2.me/theorems/ddc256a6-376f-4137-bb23-b0d987fb0f8f
-- title:
--   No-feedback hypothesis-testing converse
-- statement:
--   Let $n\ge1$ be the blocklength, $d\ge2$ the input dimension, and $p\in[0,1]$ the erasure probability. Each use of $\mathcal E_p$ transmits the input unchanged with probability $1-p$ and otherwise returns a one-dimensional orthogonal erasure flag. Write $w_S=(1-p)^{|S|}p^{n-|S|}$, $D_S=d^{|S|}$, and $b_k=\binom nk(1-p)^kp^{n-k}$. For a unit vector $\psi\in\mathbb C^d$, put $\omega_\psi=\mathcal E_p^{\otimes n}((|\psi\rangle\langle\psi|)^{\otimes n})$. For a probability distribution $q=(q_S)$ on all survivor sets, including the empty set, put $\sigma_q=\bigoplus_S q_S I_S/D_S$. For density operators $\omega,\sigma$ and $0\le\varepsilon<1$, define $\beta_\varepsilon(\omega\Vert\sigma)=\min\{\operatorname{Tr}(T\sigma):0\le T\le I,\operatorname{Tr}(T\omega)\ge1-\varepsilon\}$ and $D_H^\varepsilon=-\log_2\beta_\varepsilon$, with $-\log_2 0=+\infty$. Consider any no-feedback code for $M\ge1$ equiprobable messages, with arbitrary mixed states entangled across the inputs and an unrestricted collective POVM. If its average error is at most $\varepsilon$, then
--
--   $$\log_2 M\le\inf_q D_H^\varepsilon(\omega_\psi\Vert\sigma_q).$$
--
--   The same bound holds when every individual-message error is at most $\varepsilon$. This is an upper bound on communication, without an attainment claim.
-- source:
--   Finite-blocklength classical communication over the quantum erasure channel with and without classical feedback, arXiv:2610.00440v1, PDF p. 21, Proposition 5.2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

/-- Proposition 5.2, PDF p.21: testing converse for arbitrary mixed and entangled no-feedback codes. -/
theorem noFeedbackTestingConverse (n d M : ℕ) (hn : 0<n) (hd : 2≤d) (hM : 0<M)
    (p ε : ℝ) (hp0 : 0≤p) (hp1 : p≤1) (hε0 : 0≤ε) (hε1 : ε<1)
    (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖=1) (C : QuantumCode n d M) :
    (1-ε ≤ quantumAverage p C → (Real.logb 2 M : EReal) ≤ auxiliaryInf n d p ε ψ) ∧
    ((∀ m, 1-ε ≤ quantumIndividual p C m) →
      (Real.logb 2 M : EReal) ≤ auxiliaryInf n d p ε ψ) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P58
