-- Prove2me | Theorems.Thm_RaritaSchwinger_massive_polarization_count
-- name    : RaritaSchwinger.massive_polarization_count
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T11:18:41.174335+00:00
-- url     : https://prove2.me/theorems/a43b3608-0903-4e58-a691-9bc37141b3b5
-- title:
--   A massive Rarita–Schwinger plane wave has $2s+1=4$ polarizations
-- statement:
--   Let $\gamma^\mu$ be gamma matrices for $\eta=\mathrm{diag}(1,-1,-1,-1)$, let $m>0$, and let $p=(p_\mu)$ be a real covector on the mass shell,
--   $$p_0^2-p_1^2-p_2^2-p_3^2=m^2 .$$
--   Consider plane waves $\psi_\nu(x)=u_\nu\,e^{ip_\mu x^\mu}$ with polarization $u=(u_0,u_1,u_2,u_3)\in(\mathbb C^4)^4$. Then the set of polarizations $u$ for which $\psi$ solves the massive Rarita–Schwinger equation
--   $$\bigl(\epsilon^{\mu\kappa\rho\nu}\gamma_5\gamma_\kappa\partial_\rho-im\sigma^{\mu\nu}\bigr)\psi_\nu=0$$
--   is a complex linear subspace of $(\mathbb C^4)^4\cong\mathbb C^{16}$ of dimension exactly $4=2s+1$, $s=3/2$.
--
--   Of the $16$ components of the vector-spinor only four survive: the four physical polarizations of a massive spin-$3/2$ particle.
--
--   **Formalization Note** The source's count of physical degrees of freedom is formalized as the dimension of the space of plane-wave polarizations at a fixed on-shell momentum (of either sign of energy). The statement asserts the existence of a 4-dimensional subspace whose members are exactly the solving polarizations.
-- source:
--   "Rarita–Schwinger equation", Wikipedia, revision oldid=1362709293, https://en.wikipedia.org/w/index.php?title=Rarita%E2%80%93Schwinger_equation&oldid=1362709293; section 'Massive field and constraints' ($2s+1=4$) and section 'Interactions and the Velo–Zwanziger problem' ('the four physical polarizations of a massive spin-3/2 particle').

import Definitions.Def_RaritaSchwinger_core

open DiracEquation

namespace RaritaSchwinger

theorem massive_polarization_count (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hg : IsGammaFamily g) (m : ℝ) (hm : 0 < m) (p : Fin 4 → ℝ)
    (hp : p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 = m ^ 2) :
    ∃ V : Submodule ℂ (Fin 4 → Fin 4 → ℂ), Module.finrank ℂ V = 4 ∧
      ∀ u, u ∈ V ↔ IsMassiveRSSolution g m (vectorSpinorPlaneWave p u) := by sorry

end RaritaSchwinger
