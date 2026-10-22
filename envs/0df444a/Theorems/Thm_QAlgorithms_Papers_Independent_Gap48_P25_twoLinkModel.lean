-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P25_twoLinkModel
-- name    : QAlgorithms.Papers.Independent.Gap48.P25.twoLinkModel
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:49:29.321249+00:00
-- url     : https://prove2.me/theorems/284b156a-9572-47e0-ab83-ce9c1b2a97ee
-- title:
--   Appendix B.2.b: two-link mean-cycle toy rate, Eq.(B2)
-- statement:
--   Let $\ell,c,T_M>0$, $0<t\le1$, $0<\eta\le1$, $N\ge1$ modes, and memory coupling and Bell-detector probabilities $p_M,\eta_M\in[0,1]$. In the source's perfect-pair, noiseless-link mean-cycle model put $x=1-(1-\sqrt t\eta)^N$ and use the exact footnote-75 mean to define $\tau=(\ell/c)(3-2x)/(x(2-x))$. Both $x$ and $\tau$ are positive and $x\le1$. The sharp cutoff model assigns
--
--   $$R_2=\begin{cases}\tau^{-1}p_M^2\eta_M^2/2,&\tau<T_M,\\0,&\tau\ge T_M.\end{cases}$$
--
--   For fixed $N$ and per-mode success $z\downarrow0$, $[(\ell/c)\mathbb E M_{1-(1-z)^N}](Nz)/(\ell/c)\to3/2$. Thus the source's small-success approximation is separate from the exact mean, rather than asserted at $x=1$. The cutoff concerns a model mean, not stochastic memory-expiration histories.
-- source:
--   The Security of Practical Quantum Key Distribution, arXiv:0802.4155v3, PDF p. 46, Appendix B.2.b: two-link mean-cycle toy rate, Eq.(B2)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P25

open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Eq.(B2), PDF pp.46–47: exact-footnote-mean version of the mean-cutoff toy
rate. The printed rare-success approximation for tau is replaced by the exact
footnote-75 mean, since x=1 takes one round. The separate limit preserves the
printed 3/2 approximation; the lifetime test remains a strict cutoff on the mean. -/
theorem twoLinkModel (ell c t eta : ℝ) (N : ℕ) (life pM etaM : ℝ)
    (hell : 0 < ell) (hc : 0 < c) (ht : 0 < t ∧ t ≤ 1)
    (heta : 0 < eta ∧ eta ≤ 1) (hN : 0 < N) (hlife : 0 < life)
    (hpM : pM ∈ Set.Icc (0 : ℝ) 1) (hetaM : etaM ∈ Set.Icc (0 : ℝ) 1) :
    let x := modeSuccess t eta N
    let tau := cycleTime ell c t eta N
    0 < x ∧ x ≤ 1 ∧ 0 < tau ∧ tau = (ell/c)*(3-2*x)/(x*(2-x)) ∧
    (tau < life → repeaterRate ell c t eta N life pM etaM = tau⁻¹*(pM^2*etaM^2/2)) ∧
    (life ≤ tau → repeaterRate ell c t eta N life pM etaM = 0) ∧
    Tendsto (fun z : ℝ => ((ell/c)*waitingMean (1-(1-z)^N))*((N : ℝ)*z)/(ell/c))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (3/2)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P25

end
