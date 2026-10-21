-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_minimumComposition
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.minimumComposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:46:34.216402+00:00
-- url     : https://prove2.me/theorems/660f382f-bb58-4ba7-80ac-2cdbe6b0e4cf
-- title:
--   Pure-input reduction and composition monotonicity
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   Let $\mathcal C,\mathcal D$ be normal CPTP maps on oscillator trace class, represented by countable normalized Kraus families. Then
--   $$
--   m(\mathcal C)=\inf_{\|u\|=1}S(\mathcal C(|u\rangle\langle u|)),\qquad m(\mathcal D\circ\mathcal C)\ge m(\mathcal D).
--   $$
--   If any density operator attains $m(\mathcal C)$, some normalized pure input attains the same value. An attaining input is not asserted for an arbitrary channel.
--
--   This isolates the unrestricted infimum reduction and the channel-composition comparison.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 2, Eq.(11) and pure-input reduction

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF p.2, Eqs.(10)–(11): composition and pure-input reduction.
Printed: Eq.(10) writes min and the prose says it can be achieved by a pure input.
Changed: use the unrestricted infimum, with pure attainment conditional on attainment.
Why: concavity reduces to pure inputs but does not ensure attainment for an arbitrary
infinite-dimensional channel. No concrete attaining coherent witness is removed. -/
theorem minimumComposition (C D : B.FockOperator → B.FockOperator)
    (hC : IsNormalFockChannel C) (hD : IsNormalFockChannel D) :
    minimumEntropy C = pureMinimumEntropy C ∧
    minimumEntropy D ≤ minimumEntropy (D ∘ C) ∧
    ((∃ X, B.IsDensity X ∧ fockEntropyNats (C X) = minimumEntropy C) →
      ∃ u : B.Fock, ‖u‖ = 1 ∧ fockEntropyNats (C (pureState u)) = minimumEntropy C) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
