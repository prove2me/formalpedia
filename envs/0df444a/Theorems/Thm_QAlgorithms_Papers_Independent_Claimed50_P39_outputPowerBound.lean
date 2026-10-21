-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_outputPowerBound
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.outputPowerBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:54:54.377525+00:00
-- url     : https://prove2.me/theorems/e3f49b68-dff8-4de8-93ec-b9f65a9d65cb
-- title:
--   Real-order output power trace bound
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   For every norm-one pure input $u$, noise $n>0$, and real order $z\ge1$,
--   $$\operatorname{Tr}\!\left[(\mathcal N_n(|u\rangle\langle u|))^z\right]\le\frac1{z n^{z-1}}.$$
--   The left side is the nonnegative sum of real powers of the actual output eigenvalues. At $z=1$ the right side is one.
--
--   This is the directly derived real-order bound, not the stronger exact integer-order minimum from the companion paper.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 7, §IV.A, Eqs.(44)–(46): real-order output power bound

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF pp.6–7, Eqs.(44)–(46): real-order power bound on normalized pure inputs. -/
theorem outputPowerBound (n z : ℝ) (hn : 0 < n) (hz : 1 ≤ z)
    (u : B.Fock) (hu : ‖u‖ = 1) :
    fockRealPowerTrace (displacementNoiseChannel n (pureState u)) z ≤
      ENNReal.ofReal (1 / (z * Real.rpow n (z - 1))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
