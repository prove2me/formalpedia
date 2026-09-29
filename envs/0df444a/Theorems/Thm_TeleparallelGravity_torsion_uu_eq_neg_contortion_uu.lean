-- Prove2me | Theorems.Thm_TeleparallelGravity_torsion_uu_eq_neg_contortion_uu
-- name    : TeleparallelGravity.torsion_uu_eq_neg_contortion_uu
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T22:44:29.185324+00:00
-- url     : https://prove2.me/theorems/2ed5bae3-5f79-47ae-8966-3819bec5dc4e
-- title:
--   Identity $T^\lambda{}_{\mu\rho}u_\lambda u^\rho=-K^\lambda{}_{\mu\rho}u_\lambda u^\rho$ (Eq. (19))
-- statement:
--   For every smooth tetrad on $\mathbb R^4$ that is invertible at every point, every point $x$, every index $\mu$ and every vector $u^\rho\in\mathbb R^4$ (in the paper, the four-velocity), with $u_\lambda=g_{\lambda\alpha}u^\alpha$:
--   $$T^\lambda{}_{\mu\rho}\,u_\lambda u^\rho=-K^\lambda{}_{\mu\rho}\,u_\lambda u^\rho.$$
-- source:
--   R. Aldrovandi, J. G. Pereira, K. H. Vu, "Selected Topics in Teleparallel Gravity", Brazilian Journal of Physics 34 (2004), no. 4A, 1374-1380, https://doi.org/10.1590/S0103-97332004000700009 — Identity $T^\lambda{}_{\mu\rho}u_\lambda u^\rho=-K^\lambda{}_{\mu\rho}u_\lambda u^\rho$ (Eq. (19))

import Mathlib
import Definitions.Def_TeleparallelGravity_Defs

open scoped ContDiff

namespace TeleparallelGravity
theorem torsion_uu_eq_neg_contortion_uu (h : TetradField) (hh : IsTetrad h)
    (u : Fin 4 → ℝ) (μ : Fin 4) (x : Spacetime) :
    ∑ l, ∑ ρ, torsion h l μ ρ x * (∑ α, metric h x l α * u α) * u ρ =
      -∑ l, ∑ ρ, contortion h l μ ρ x * (∑ α, metric h x l α * u α) * u ρ := by
  sorry
end TeleparallelGravity
