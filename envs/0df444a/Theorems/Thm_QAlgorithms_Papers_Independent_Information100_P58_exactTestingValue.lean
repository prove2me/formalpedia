-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P58_exactTestingValue
-- name    : QAlgorithms.Papers.Independent.Information100.P58.exactTestingValue
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:15:38.186148+00:00
-- url     : https://prove2.me/theorems/03a6b370-184c-48d3-81c4-7a152777a40f
-- title:
--   Exact testing value and explicit auxiliary optimizer
-- statement:
--   Let $n\ge1$ be the blocklength, $d\ge2$ the input dimension, and $p\in[0,1]$ the erasure probability. Each use of $\mathcal E_p$ transmits the input unchanged with probability $1-p$ and otherwise returns a one-dimensional orthogonal erasure flag. Write $w_S=(1-p)^{|S|}p^{n-|S|}$, $D_S=d^{|S|}$, and $b_k=\binom nk(1-p)^kp^{n-k}$. For a unit vector $\psi\in\mathbb C^d$, put $\omega_\psi=\mathcal E_p^{\otimes n}((|\psi\rangle\langle\psi|)^{\otimes n})$. For a probability distribution $q=(q_S)$ on all survivor sets, including the empty set, put $\sigma_q=\bigoplus_S q_S I_S/D_S$. For density operators $\omega,\sigma$ and $0\le\varepsilon<1$, define $\beta_\varepsilon(\omega\Vert\sigma)=\min\{\operatorname{Tr}(T\sigma):0\le T\le I,\operatorname{Tr}(T\omega)\ge1-\varepsilon\}$ and $D_H^\varepsilon=-\log_2\beta_\varepsilon$, with $-\log_2 0=+\infty$. Set $B_j=\sum_{k=0}^j b_k$, $Z_j=\sum_{k=0}^j b_kd^k$, and $R_\varepsilon=\min_{0\le j\le n:B_j>\varepsilon} Z_j/(B_j-\varepsilon)$. Then
--
--   $$\inf_q D_H^\varepsilon(\omega_\psi\Vert\sigma_q)=\log_2R_\varepsilon.$$
--
--   For every minimizing cutoff $j_*$ with $B_{j_*}>\varepsilon$, the nonnegative weights
--
--   $$q_S^*=\frac{w_SD_S\mathbf1\{|S|\le j_*\}}{Z_{j_*}}$$
--
--   sum to one, attain the infimum, and satisfy
--
--   $$\beta_\varepsilon(\omega_\psi\Vert\sigma_{q^*})=\frac{B_{j_*}-\varepsilon}{Z_{j_*}}=\frac1{R_\varepsilon}.$$
--
--   This evaluates the actual quantum testing problem, including endpoint channels and zero tolerance.
-- source:
--   Finite-blocklength classical communication over the quantum erasure channel with and without classical feedback, arXiv:2610.00440v1, PDF p. 22, Theorem 5.4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

/-- Theorem 5.4, PDF pp.22–23: exact value, explicit optimizing distribution, and its type-II value. -/
theorem exactTestingValue (n d : ℕ) (hn : 0<n) (hd : 2≤d) (p ε : ℝ)
    (hp0 : 0≤p) (hp1 : p≤1) (hε0 : 0≤ε) (hε1 : ε<1)
    (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖=1) :
    auxiliaryInf n d p ε ψ = (Real.logb 2 (messageThreshold n d p ε) : EReal) ∧
    ∀ j : ℕ, j≤n → ε<cumulativeB n p j →
      cumulativeZ n d p j / (cumulativeB n p j-ε) = messageThreshold n d p ε →
      (∀ S, 0≤optimizer n d p j S) ∧ (∑ S, optimizer n d p j S)=1 ∧
      testingD ε (reference n d p ψ) (auxiliary n d (optimizer n d p j)) = auxiliaryInf n d p ε ψ ∧
      testingBeta ε (reference n d p ψ) (auxiliary n d (optimizer n d p j)) =
        (cumulativeB n p j-ε)/cumulativeZ n d p j ∧
      (cumulativeB n p j-ε)/cumulativeZ n d p j = 1/messageThreshold n d p ε := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P58
