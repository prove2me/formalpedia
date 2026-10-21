-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_thermalParameterOrder
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.thermalParameterOrder
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:50:24.768975+00:00
-- url     : https://prove2.me/theorems/1da1d576-7570-4f33-9e04-7c89a2bb947c
-- title:
--   Thermal minimum-entropy parameter ordering
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   For two admissible parameter pairs $(\eta,N),(\eta',N')$,
--   $$m(\mathcal E_\eta^N)\ge m(\mathcal E_{\eta'}^N)\quad(\eta\le\eta').$$
--   More generally $m(\mathcal E_\eta^N)\ge m(\mathcal E_{\eta'}^{N'})$ under either condition
--   $$\eta\le\eta',\quad(1-\eta')N'\le(1-\eta)N,$$
--   $$\eta'\le\eta,\quad(1-\eta')N'\le(1-\eta)N+\eta'-\eta.$$
--   These cross-multiplied conditions retain the valid endpoint cases without dividing by $1-\eta$ or $1-\eta'$.
--
--   The ordering concerns channel infima, rather than every fixed input's entropy.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 4, Eqs.(23)–(25): thermal minimum-entropy ordering

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF p.4, Eqs.(23)–(25): minimum-entropy ordering. Eq.(25) has
+etaOther-eta; cross-multiplied conditions avoid endpoint quotients. -/
theorem thermalParameterOrder (eta etaOther N NOther : ℝ)
    (he0 : 0 ≤ eta) (he1 : eta ≤ 1) (heo0 : 0 ≤ etaOther) (heo1 : etaOther ≤ 1)
    (hN : 0 ≤ N) (hNo : 0 ≤ NOther) :
    (eta ≤ etaOther → minimumEntropy (thermal etaOther N) ≤ minimumEntropy (thermal eta N)) ∧
    (eta ≤ etaOther → (1 - etaOther) * NOther ≤ (1 - eta) * N →
      minimumEntropy (thermal etaOther NOther) ≤ minimumEntropy (thermal eta N)) ∧
    (etaOther ≤ eta → (1 - etaOther) * NOther ≤ (1 - eta) * N + etaOther - eta →
      minimumEntropy (thermal etaOther NOther) ≤ minimumEntropy (thermal eta N)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
