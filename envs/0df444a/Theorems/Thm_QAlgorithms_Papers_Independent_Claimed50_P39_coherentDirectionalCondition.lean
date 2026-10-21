-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_coherentDirectionalCondition
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.coherentDirectionalCondition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:58:41.409248+00:00
-- url     : https://prove2.me/theorems/aecac610-6c81-4688-a75d-93ef2af941ea
-- title:
--   Coherent mixed-direction derivative and energy law
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   Let $\sigma$ be a density, $\alpha\in\mathbb C$, $\widetilde\sigma=D(-\alpha)\sigma D(-\alpha)^\dagger$ have finite photon mean $E$, and $\sigma(t)=(1-t)|\alpha\rangle\langle\alpha|+t\sigma$. For $(\mathcal C,\zeta,M)=(\mathcal N_n,1,n)$ with $n>0$, or $(\mathcal E_\eta^N,\eta,(1-\eta)N)$ with $M>0$,
--   $$\langle a^\dagger a\rangle_{\mathcal C(\widetilde\sigma)}=\zeta E+M,\qquad
--   \left.\frac{d}{dt}S(\mathcal C(\sigma(t)))\right|_{0+}=\zeta E\ln\frac{M+1}M\ge0.$$
--   The output photon moment is finite, and the output entropy along $0\le t\le1$ is finite. The logarithm sign corrects the printed Eq.(53), as required by its first trace line.
--
--   This gives a necessary directional condition only, not a sufficient neighborhood minimum.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 8, §V.A, Eqs.(53)–(54): coherent mixed-direction derivative

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF p.8, Eqs.(53)–(54): coherent mixed-direction necessary condition,
on positive-noise finite-centered-energy inputs. Printed ln(M/(M+1)) has the
wrong sign: the first trace line gives ln((M+1)/M). This correction requires
independent moderation and is not a sufficient local-minimum theorem. -/
theorem coherentDirectionalCondition (eta N n : ℝ) (he0 : 0 ≤ eta) (he1 : eta ≤ 1)
    (hN : 0 ≤ N) (hn : 0 ≤ n) (alpha : ℂ) (X : B.FockOperator) (hX : B.IsDensity X)
    (hE : FiniteEnergy (conjugateBy (B.displacement (-alpha)) X)) :
    (0 < n → CoherentDerivative (displacementNoiseChannel n) 1 n alpha X) ∧
    (0 < (1 - eta) * N → CoherentDerivative (thermal eta N) eta ((1 - eta) * N) alpha X) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
