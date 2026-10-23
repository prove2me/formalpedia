-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_gaussianComposition
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.gaussianComposition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:03:44.856127+00:00
-- url     : https://prove2.me/theorems/4968ab57-170e-4db9-8962-81f937fda01e
-- title:
--   Gaussian composition including displacement
-- statement:
--   Work on the complete one-mode Fock space, with $[Q,P]=i$, and let $\Phi$ be a trace-class CPTP Gaussian channel. Its real data $(K,\alpha,m)$ act on every input density through $\chi_{\Phi(\rho)}(z)=\chi_\rho(Kz)\exp(-z^T\alpha z/2+im^Tz)$, where $z\in\mathbb R^2$, $\alpha$ is symmetric positive semidefinite, and $\det\alpha\ge((\det K-1)/2)^2$. Let $\Phi_1,\Phi_2$ have data $(K_1,\alpha_1,m_1)$ and $(K_2,\alpha_2,m_2)$ respectively. Their Schrodinger composition $\Phi_2\circ\Phi_1$ is Gaussian CPTP with
--
--   $$K=K_1K_2,\qquad \alpha=K_2^T\alpha_1K_2+\alpha_2,\qquad m=K_2^Tm_1+m_2.$$
--
--   The reversed argument-matrix order and the displacement transport are part of the composition rule.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 7, (2.6)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P49

noncomputable section

open scoped BigOperators ENNReal Topology

open Filter MeasureTheory

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

namespace QAlgorithms.Papers.Independent.Claimed50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Equation (2.6), PDF p.7: K1*K2, transported noise, AND displacement. -/
theorem gaussianComposition (E1 E2 : FockMap) (g1 g2 : GaussianData)
    (h1 : IsGaussianChannel E1 g1) (h2 : IsGaussianChannel E2 g2) :
    IsGaussianChannel (E2 ∘ E1) (composeData g1 g2) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
