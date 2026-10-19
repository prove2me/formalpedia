-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P58_optimizedTestingConverse
-- name    : QAlgorithms.Papers.Independent.Information100.P58.optimizedTestingConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:16:22.246972+00:00
-- url     : https://prove2.me/theorems/5fd0e4e0-8e91-4fe2-af14-f8ea60659ccb
-- title:
--   Fully optimized classical–quantum testing converse
-- statement:
--   Let $n\ge1$ be the blocklength, $d\ge2$ the input dimension, and $p\in[0,1]$ the erasure probability. Each use of $\mathcal E_p$ transmits the input unchanged with probability $1-p$ and otherwise returns a one-dimensional orthogonal erasure flag. Write $w_S=(1-p)^{|S|}p^{n-|S|}$, $D_S=d^{|S|}$, and $b_k=\binom nk(1-p)^kp^{n-k}$. For density operators $\omega,\sigma$ and $0\le\varepsilon<1$, define $\beta_\varepsilon(\omega\Vert\sigma)=\min\{\operatorname{Tr}(T\sigma):0\le T\le I,\operatorname{Tr}(T\omega)\ge1-\varepsilon\}$ and $D_H^\varepsilon=-\log_2\beta_\varepsilon$, with $-\log_2 0=+\infty$. Set $B_j=\sum_{k=0}^j b_k$, $Z_j=\sum_{k=0}^j b_kd^k$, and $R_\varepsilon=\min_{0\le j\le n:B_j>\varepsilon} Z_j/(B_j-\varepsilon)$. For each finite input ensemble $E=(p_x,\rho^x)$, allowing nonuniform probabilities and mixed entangled inputs, set $\Theta_E=\sum_xp_x|x\rangle\langle x|\otimes\mathcal E_p^{\otimes n}(\rho^x)$ and $\pi_E=\sum_xp_x|x\rangle\langle x|$. Define $\chi_H^\varepsilon=\sup_E\inf_\sigma D_H^\varepsilon(\Theta_E\Vert\pi_E\otimes\sigma)$, where $\sigma$ ranges over every output density operator. Then
--
--   $$\chi_H^\varepsilon(\mathcal E_p^{\otimes n})=\log_2R_\varepsilon.$$
--
--   The uniform ensemble of all $d^n$ computational-basis product states attains the supremum. The quantity evaluated is a testing converse expression, rather than a definition of operational capacity.
-- source:
--   Finite-blocklength classical communication over the quantum erasure channel with and without classical feedback, arXiv:2610.00440v1, PDF p. 23, Proposition 5.5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

/-- Proposition 5.5, PDF p.23 (Appendix A, pp.45–46): fully optimized cq converse and attaining ensemble. -/
theorem optimizedTestingConverse (n d : ℕ) (hn : 0<n) (hd : 2≤d) (p ε : ℝ)
    (hp0 : 0≤p) (hp1 : p≤1) (hε0 : 0≤ε) (hε1 : ε<1) :
    optimizedConverse n d p ε = (Real.logb 2 (messageThreshold n d p ε) : EReal) ∧
    basisEnsembleInf n d p ε = optimizedConverse n d p ε := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P58
