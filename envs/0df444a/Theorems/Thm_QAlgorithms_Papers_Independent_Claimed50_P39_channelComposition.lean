-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_channelComposition
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.channelComposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:48:45.189162+00:00
-- url     : https://prove2.me/theorems/37e2e921-e6c3-4bd9-a72a-d283e09f538e
-- title:
--   Noise-channel composition identities
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   All identities below hold on every density operator. For $n_1,n_2\ge0$,
--   $$\mathcal N_{n_2}\circ\mathcal N_{n_1}=\mathcal N_{n_1+n_2}.$$
--   For admissible $\eta_i,N_i$ with $\eta_1\eta_2<1$,
--   $$\mathcal E_{\eta_2}^{N_2}\circ\mathcal E_{\eta_1}^{N_1}=\mathcal E_{\eta_1\eta_2}^{N'},\quad N'=\frac{\eta_2(1-\eta_1)N_1+(1-\eta_2)N_2}{1-\eta_1\eta_2}.$$
--   If $\eta_1\eta_2=1$ this composition is the identity. Moreover,
--   $$\mathcal E_{\eta_1}^{N_1}=\mathcal N_{(1-\eta_1)N_1}\circ\mathcal E_{\eta_1}^{0},\quad
--   \mathcal E_{\eta_1}^{N_1}=\mathcal E_{\eta_1}^{0}\circ\mathcal N_{(1-\eta_1)N_1/\eta_1}\quad(\eta_1>0).$$
--   These are equalities of physical channel actions on all states.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 4, Eqs.(18)–(20): composition laws

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF p.4, Eqs.(18)–(20): composition on all densities. Product-one
transmissivity gives identity; quotient decompositions use positive denominators. -/
theorem channelComposition (eta1 eta2 N1 N2 n1 n2 : ℝ)
    (he10 : 0 ≤ eta1) (he11 : eta1 ≤ 1) (he20 : 0 ≤ eta2) (he21 : eta2 ≤ 1)
    (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2) (hn1 : 0 ≤ n1) (hn2 : 0 ≤ n2)
    (X : B.FockOperator) (hX : B.IsDensity X) :
    displacementNoiseChannel n2 (displacementNoiseChannel n1 X) = displacementNoiseChannel (n1 + n2) X ∧
    (eta1 * eta2 < 1 → thermal eta2 N2 (thermal eta1 N1 X) =
      thermal (eta1 * eta2)
        ((eta2 * (1 - eta1) * N1 + (1 - eta2) * N2) / (1 - eta1 * eta2)) X) ∧
    (eta1 * eta2 = 1 → thermal eta2 N2 (thermal eta1 N1 X) = X) ∧
    thermal eta1 N1 X = displacementNoiseChannel ((1 - eta1) * N1) (thermal eta1 0 X) ∧
    (0 < eta1 → thermal eta1 N1 X = thermal eta1 0 (displacementNoiseChannel (((1 - eta1) * N1) / eta1) X)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
