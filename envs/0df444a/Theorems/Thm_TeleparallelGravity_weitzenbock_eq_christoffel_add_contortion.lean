-- Prove2me | Theorems.Thm_TeleparallelGravity_weitzenbock_eq_christoffel_add_contortion
-- name    : TeleparallelGravity.weitzenbock_eq_christoffel_add_contortion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T22:41:16.24525+00:00
-- url     : https://prove2.me/theorems/53e5a44b-4128-4d15-ba2a-22887a59588c
-- title:
--   Weitzenböck = Christoffel + contortion, $\Gamma^\rho{}_{\mu\nu}=\mathring\Gamma^\rho{}_{\mu\nu}+K^\rho{}_{\mu\nu}$ (Eq. (8))
-- statement:
--   For every smooth tetrad $h^a{}_\mu$ on $\mathbb R^4$ that is invertible at every point, the Weitzenböck connection decomposes as
--   $$\Gamma^\rho{}_{\mu\nu}=\mathring\Gamma^\rho{}_{\mu\nu}+K^\rho{}_{\mu\nu},$$
--   where $\mathring\Gamma$ is the Christoffel connection of the metric $g_{\mu\nu}=\eta_{ab}h^a{}_\mu h^b{}_\nu$ and $K^\rho{}_{\mu\nu}=\tfrac12(T_\mu{}^\rho{}_\nu+T_\nu{}^\rho{}_\mu-T^\rho{}_{\mu\nu})$ is the contortion (Eq. (9)).
-- source:
--   R. Aldrovandi, J. G. Pereira, K. H. Vu, "Selected Topics in Teleparallel Gravity", Brazilian Journal of Physics 34 (2004), no. 4A, 1374-1380, https://doi.org/10.1590/S0103-97332004000700009 — Weitzenböck = Christoffel + contortion, $\Gamma^\rho{}_{\mu\nu}=\mathring\Gamma^\rho{}_{\mu\nu}+K^\rho{}_{\mu\nu}$ (Eq. (8))

import Mathlib
import Definitions.Def_TeleparallelGravity_Defs

open scoped ContDiff

namespace TeleparallelGravity
theorem weitzenbock_eq_christoffel_add_contortion (h : TetradField) (hh : IsTetrad h)
    (ρ μ ν : Fin 4) (x : Spacetime) :
    weitzenbock h ρ μ ν x = christoffel h ρ μ ν x + contortion h ρ μ ν x := by
  sorry
end TeleparallelGravity
