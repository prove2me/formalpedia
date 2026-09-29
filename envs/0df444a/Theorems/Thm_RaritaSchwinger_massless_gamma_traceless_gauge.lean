-- Prove2me | Theorems.Thm_RaritaSchwinger_massless_gamma_traceless_gauge
-- name    : RaritaSchwinger.massless_gamma_traceless_gauge
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T11:18:04.475311+00:00
-- url     : https://prove2.me/theorems/82f9671d-6fa4-4cd7-88ae-e28bde7e0010
-- title:
--   Massless Rarita–Schwinger field in the gamma-traceless gauge: $\gamma^\nu\partial_\nu\psi_\mu=0$, $\partial^\mu\psi_\mu=0$
-- statement:
--   Let $\gamma^\mu$ be gamma matrices for the metric $\eta=\mathrm{diag}(1,-1,-1,-1)$ and let $\psi_\mu$ be a continuously differentiable vector-spinor field on $\mathbb R^4$ that solves the massless Rarita–Schwinger equation $\gamma^{\mu\nu\rho}\partial_\nu\psi_\rho=0$ and satisfies the gamma-traceless gauge condition $\gamma^\mu\psi_\mu=0$ everywhere. Then at every point $x$:
--   1. $\gamma^\nu\partial_\nu\psi_\mu(x)=0$ for every $\mu$ (Dirac-type condition);
--   2. $\partial^\mu\psi_\mu(x)=0$ (transversality);
--   3. $\gamma^\mu\psi_\mu(x)=0$.
--
--   These equations describe the two helicity states of a massless spin-$3/2$ field.
--
--   **Formalization Note** The gauge condition is a hypothesis on $\psi$ (the gauge has already been imposed); $\partial^\mu\psi_\mu=\sum_\mu\eta^{\mu\mu}\partial_\mu\psi_\mu$.
-- source:
--   "Rarita–Schwinger equation", Wikipedia, revision oldid=1362709293, https://en.wikipedia.org/w/index.php?title=Rarita%E2%80%93Schwinger_equation&oldid=1362709293; section 'Massless equation and gauge invariance', gamma-traceless gauge and the conditions $\gamma^\nu\partial_\nu\psi_\mu=0$, $\partial^\mu\psi_\mu=0$, $\gamma^\mu\psi_\mu=0$.

import Definitions.Def_RaritaSchwinger_core

open DiracEquation

namespace RaritaSchwinger

theorem massless_gamma_traceless_gauge (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hg : IsGammaFamily g) (psi : VectorSpinorField) (hpsi : ContDiff ℝ 1 psi)
    (hEq : IsMasslessRSSolution g psi) (hgauge : ∀ x, gammaTrace g psi x = 0) :
    ∀ x, (∀ mu, diracOperator g psi mu x = 0) ∧ divergence psi x = 0 ∧
      gammaTrace g psi x = 0 := by sorry

end RaritaSchwinger
