-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_coherentOutput
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.coherentOutput
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:45:39.53829+00:00
-- url     : https://prove2.me/theorems/a8aa7534-a90e-480b-87fe-d0991f789d05
-- title:
--   Coherent outputs and attained entropy upper bounds
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   Let $\tau_M$ have photon probabilities $(M/(M+1))^j/(M+1)$, and let $D(\alpha)$ be Weyl displacement. For every coherent amplitude $\alpha\in\mathbb C$,
--   $$
--   \mathcal E_\eta^N(|\alpha\rangle\langle\alpha|)=D(\sqrt\eta\alpha)\tau_{(1-\eta)N}D(\sqrt\eta\alpha)^\dagger,\qquad
--   \mathcal N_n(|\alpha\rangle\langle\alpha|)=D(\alpha)\tau_nD(\alpha)^\dagger.
--   $$
--   The vacuum outputs are respectively $\tau_{(1-\eta)N}$ and $\tau_n$. Their entropies, and those of every coherent output, are $g((1-\eta)N)$ and $g(n)$. These attained values are upper bounds for the respective unrestricted infima. Coherent vectors, displacements and thermal operators have their actual normalized/unitary realizations, including $\tau_0=|0\rangle\langle0|$.
--
--   This gives attaining candidates and upper bounds without asserting the conjectured lower bounds.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 2, Eqs.(7)–(9), Appendix A: coherent outputs and attained upper bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF pp.2–3, Eqs.(7)–(9), Appendix A: coherent outputs and attained upper
bounds, including the vacuum coefficient one when the mean is zero. -/
theorem coherentOutput (eta N n : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1)
    (hN : 0 ≤ N) (hn : 0 ≤ n) (alpha : ℂ) :
    B.CoherentRealized ∧ B.DisplacementRealized ∧
    B.ThermalRealized (2 * N + 1) ∧ B.ThermalRealized (2 * n + 1) ∧
    B.ThermalRealized (2 * ((1 - eta) * N) + 1) ∧
    thermal eta N (B.fockDyad 0 0) = photonMeanThermalState ((1 - eta) * N) ∧
    displacementNoiseChannel n (B.fockDyad 0 0) = photonMeanThermalState n ∧
    thermal eta N (B.coherentProjector alpha) =
      conjugateBy (B.displacement ((Real.sqrt eta : ℂ) * alpha)) (photonMeanThermalState ((1 - eta) * N)) ∧
    displacementNoiseChannel n (B.coherentProjector alpha) = conjugateBy (B.displacement alpha) (photonMeanThermalState n) ∧
    fockEntropyNats (thermal eta N (B.coherentProjector alpha)) = ENNReal.ofReal (g ((1 - eta) * N)) ∧
    fockEntropyNats (displacementNoiseChannel n (B.coherentProjector alpha)) = ENNReal.ofReal (g n) ∧
    minimumEntropy (thermal eta N) ≤ ENNReal.ofReal (g ((1 - eta) * N)) ∧
    minimumEntropy (displacementNoiseChannel n) ≤ ENNReal.ofReal (g n) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
