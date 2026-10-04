-- Prove2me | Theorems.Thm_ProjectiveMeasurementEquilibration_relEntropy_chain_rule
-- name    : ProjectiveMeasurementEquilibration.relEntropy_chain_rule
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T16:01:37.248979+00:00
-- url     : https://prove2.me/theorems/3fe230dd-20ec-4702-b983-724891b1f62f
-- title:
--   Eq. (12) — $D(\rho\|\sigma)=D(\rho\|\mathcal P_X\rho)+D(\mathcal P_X\rho\|\sigma)$
-- statement:
--   Throughout, $n$ is a finite index type, the Hilbert space is $\mathbb C^n$, $X$ is a Hermitian $n\times n$ complex matrix with spectral decomposition $X=\sum_{x} x\,P_x$ ($x$ ranging over the distinct eigenvalues, $P_x$ the orthogonal projection onto the $x$-eigenspace, and $P_x=0$ for $x$ not an eigenvalue), and a density matrix is a positive semidefinite matrix of trace $1$. For density matrices $\rho,\sigma$ with $[\sigma,X]=0$, $$D(\rho\|\sigma)=D(\rho\|\mathcal P_X(\rho))+D(\mathcal P_X(\rho)\|\sigma)$$ as an identity in $(-\infty,+\infty]$, where $D(\rho\|\sigma)=\operatorname{tr}(\rho\log\rho)-\operatorname{tr}(\rho\log\sigma)$ if $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$ and $+\infty$ otherwise (for non-faithful $\sigma$ the identity is understood on its support).
-- source:
--   G. Carcassi (Assumptions of Physics collaboration), "Projective measurements are equilibration processes", AoP Technical Brief 017, https://assumptionsofphysics.org/resources/briefs, proof of Theorem 1, eq. (12), p. 4

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_pme_measurement_conditions

open Matrix Filter Topology

namespace ProjectiveMeasurementEquilibration

theorem relEntropy_chain_rule {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (ρ σ : Matrix n n ℂ) (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ)
    (hcomm : X * σ = σ * X) :
    relEntropy ρ σ = relEntropy ρ (pinching hX ρ) + relEntropy (pinching hX ρ) σ := by sorry

end ProjectiveMeasurementEquilibration
