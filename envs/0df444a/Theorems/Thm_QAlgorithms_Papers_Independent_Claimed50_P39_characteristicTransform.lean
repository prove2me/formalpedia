-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_characteristicTransform
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.characteristicTransform
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:48:12.184597+00:00
-- url     : https://prove2.me/theorems/875782de-70fd-4b28-bc73-d50278a708a1
-- title:
--   Characteristic functions of the constructed channels
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   For $\chi_\rho(z)=\operatorname{Tr}(\rho D(z))$ and every $z\in\mathbb C$,
--   $$
--   \chi_{\mathcal E_\eta^N(\rho)}(z)=\chi_\rho(\sqrt\eta z)e^{-(1-\eta)(N+1/2)|z|^2},\qquad
--   \chi_{\mathcal N_n(\rho)}(z)=\chi_\rho(z)e^{-n|z|^2}.
--   $$
--   The maps are the constructed normal CPTP channels and send every density to a density. Their beam-splitter coefficient sums converge; for $n>0$ every displacement coefficient integrand is integrable and has the specified output integral. Displacements have their actual unitary realizations. At the endpoints $\mathcal E_0^N(\rho)=\tau_N$, $\mathcal E_1^N(\rho)=\rho$, and $\mathcal N_0(\rho)=\rho$.
--
--   These transformation laws are conclusions about the physical channels, rather than axioms imposed on arbitrary maps.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 3, §II.B, Eq.(17): channel characteristic functions

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF pp.3–4, Eq.(17): characteristic laws from the constructed channels.
Convergence, bounded realization and density preservation are conclusions.
The Gaussian exponent is negative and includes the vacuum half quantum. -/
theorem characteristicTransform (eta N n : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1)
    (hN : 0 ≤ N) (hn : 0 ≤ n) :
    B.DisplacementRealized ∧ IsNormalFockChannel (thermal eta N) ∧ IsNormalFockChannel (displacementNoiseChannel n) ∧
    (∀ X : B.FockOperator, B.IsDensity X →
      B.IsDensity (thermal eta N X) ∧ B.IsDensity (displacementNoiseChannel n X) ∧
      (∀ m k, Summable (thermalTerm eta N X m k) ∧
        thermal eta N X (B.fockKet k) m = thermalOutputMatrix eta N X m k) ∧
      (0 < n → ∀ m k, Integrable (classicalIntegrand n X m k) ∧
        displacementNoiseChannel n X (B.fockKet k) m = ∫ z : ℂ, classicalIntegrand n X m k z) ∧
      (∀ z : ℂ, B.characteristic (thermal eta N X) z =
        B.characteristic X ((Real.sqrt eta : ℂ) * z) *
          (Real.exp (-(1 - eta) * (N + 1 / 2) * Complex.normSq z) : ℂ)) ∧
      (∀ z : ℂ, B.characteristic (displacementNoiseChannel n X) z = B.characteristic X z *
        (Real.exp (-n * Complex.normSq z) : ℂ)) ∧
      thermal 0 N X = photonMeanThermalState N ∧ thermal 1 N X = X) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
