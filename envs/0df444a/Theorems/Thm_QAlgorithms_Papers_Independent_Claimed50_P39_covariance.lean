-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_covariance
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.covariance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:47:29.856401+00:00
-- url     : https://prove2.me/theorems/ddc404b3-5932-4a37-b96a-8f927bd9a1b7
-- title:
--   Displacement and phase covariance
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   Let $R_\phi=\exp(i\phi a^\dagger a)$, $\phi\in\mathbb R$, and let $\rho$ be any density. The actual diagonal realization of $R_\phi$ is unitary. For any $\alpha\in\mathbb C$,
--   $$
--   \mathcal N_n(D(\alpha)\rho D(\alpha)^\dagger)=D(\alpha)\mathcal N_n(\rho)D(\alpha)^\dagger,
--   $$
--   $$
--   \mathcal E_\eta^N(D(\alpha)\rho D(\alpha)^\dagger)=D(\sqrt\eta\alpha)\mathcal E_\eta^N(\rho)D(\sqrt\eta\alpha)^\dagger.
--   $$
--   Both channels commute with conjugation by $R_\phi$. Conjugating an input first by $R_\phi$ and then by $D(\alpha)$ leaves either output entropy unchanged, including infinite entropy.
--
--   This identifies the displacement and phase orbits along which output entropy is constant.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 3, §II.A, Eqs.(14)–(15): displacement and phase covariance

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF p.3, Eqs.(14)–(15): displacement and phase covariance. Phase covariance
is conjugation, and displacement contracts by sqrt(eta). -/
theorem covariance (eta N n : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1)
    (hN : 0 ≤ N) (hn : 0 ≤ n) (X : B.FockOperator) (hX : B.IsDensity X)
    (alpha : ℂ) (phi : ℝ) :
    (ContinuousLinearMap.adjoint (fockPhaseRotation phi)).comp (fockPhaseRotation phi) = 1 ∧
    B.HasFockMatrix (fockPhaseRotation phi)
      (fun m k => if m = k then Complex.exp (Complex.I * (phi * k : ℝ)) else 0) ∧
    displacementNoiseChannel n (conjugateBy (B.displacement alpha) X) =
      conjugateBy (B.displacement alpha) (displacementNoiseChannel n X) ∧
    thermal eta N (conjugateBy (B.displacement alpha) X) =
      conjugateBy (B.displacement ((Real.sqrt eta : ℂ) * alpha)) (thermal eta N X) ∧
    displacementNoiseChannel n (conjugateBy (fockPhaseRotation phi) X) = conjugateBy (fockPhaseRotation phi) (displacementNoiseChannel n X) ∧
    thermal eta N (conjugateBy (fockPhaseRotation phi) X) = conjugateBy (fockPhaseRotation phi) (thermal eta N X) ∧
    fockEntropyNats (displacementNoiseChannel n (conjugateBy (B.displacement alpha) (conjugateBy (fockPhaseRotation phi) X))) =
      fockEntropyNats (displacementNoiseChannel n X) ∧
    fockEntropyNats (thermal eta N (conjugateBy (B.displacement alpha) (conjugateBy (fockPhaseRotation phi) X))) =
      fockEntropyNats (thermal eta N X) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
