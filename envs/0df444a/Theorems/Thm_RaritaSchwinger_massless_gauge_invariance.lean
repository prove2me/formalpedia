-- Prove2me | Theorems.Thm_RaritaSchwinger_massless_gauge_invariance
-- name    : RaritaSchwinger.massless_gauge_invariance
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T11:15:20.12443+00:00
-- url     : https://prove2.me/theorems/26e8bf97-41e4-4ec1-8a22-a6dc86470bc8
-- title:
--   Fermionic gauge invariance of the massless Rarita–Schwinger equation
-- statement:
--   Let $\gamma^0,\dots,\gamma^3$ be gamma matrices, $\gamma^\mu\gamma^\nu+\gamma^\nu\gamma^\mu=2\eta^{\mu\nu}I_4$ with $\eta=\mathrm{diag}(1,-1,-1,-1)$, let $\psi_\mu$ be a continuously differentiable vector-spinor field on $\mathbb R^4$, and let $\epsilon:\mathbb R^4\to\mathbb C^4$ be a spinor field of class $C^2$. Then $\psi$ solves the massless Rarita–Schwinger equation if and only if the gauge-transformed field does:
--   $$\gamma^{\mu\nu\rho}\partial_\nu\bigl(\psi_\rho+\partial_\rho\epsilon\bigr)=0\ \ \forall x,\mu\quad\Longleftrightarrow\quad\gamma^{\mu\nu\rho}\partial_\nu\psi_\rho=0\ \ \forall x,\mu .$$
--
--   In supergravity this gauge invariance is the spin-$3/2$ part of local supersymmetry; it removes the unphysical spin-$1/2$ components of the vector-spinor.
--
--   **Formalization Note** "Invariance" is stated as an equivalence of the two solution conditions; regularity ($\psi\in C^1$, $\epsilon\in C^2$) is added because derivatives are total functions in Lean.
-- source:
--   "Rarita–Schwinger equation", Wikipedia, revision oldid=1362709293, https://en.wikipedia.org/w/index.php?title=Rarita%E2%80%93Schwinger_equation&oldid=1362709293; section 'Massless equation and gauge invariance', gauge transformation $\psi_\mu\to\psi_\mu+\partial_\mu\epsilon$.

import Definitions.Def_RaritaSchwinger_core

open DiracEquation

namespace RaritaSchwinger

theorem massless_gauge_invariance (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (hg : IsGammaFamily g)
    (psi : VectorSpinorField) (hpsi : ContDiff ℝ 1 psi)
    (eps : (Fin 4 → ℝ) → (Fin 4 → ℂ)) (heps : ContDiff ℝ 2 eps) :
    IsMasslessRSSolution g (fun x mu => psi x mu + pd eps mu x) ↔
      IsMasslessRSSolution g psi := by sorry

end RaritaSchwinger
