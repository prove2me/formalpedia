-- Prove2me | Theorems.Thm_TeleparallelGravity_superpotential_antisymm
-- name    : TeleparallelGravity.superpotential_antisymm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T22:43:27.749973+00:00
-- url     : https://prove2.me/theorems/67e94fad-b200-4392-b657-4e3e007d19c9
-- title:
--   Antisymmetry of the superpotential, $S^{\rho\mu\nu}=-S^{\rho\nu\mu}$ (Eq. (11))
-- statement:
--   For every smooth tetrad on $\mathbb R^4$ that is invertible at every point, the superpotential $S^{\rho\mu\nu}=\tfrac12[K^{\mu\nu\rho}-g^{\rho\nu}T^{\sigma\mu}{}_\sigma+g^{\rho\mu}T^{\sigma\nu}{}_\sigma]$ of Eq. (11) is antisymmetric in its last two indices: $S^{\rho\mu\nu}=-S^{\rho\nu\mu}$.
-- source:
--   R. Aldrovandi, J. G. Pereira, K. H. Vu, "Selected Topics in Teleparallel Gravity", Brazilian Journal of Physics 34 (2004), no. 4A, 1374-1380, https://doi.org/10.1590/S0103-97332004000700009 — Antisymmetry of the superpotential, $S^{\rho\mu\nu}=-S^{\rho\nu\mu}$ (Eq. (11))

import Mathlib
import Definitions.Def_TeleparallelGravity_Defs

open scoped ContDiff

namespace TeleparallelGravity
theorem superpotential_antisymm (h : TetradField) (hh : IsTetrad h)
    (ρ μ ν : Fin 4) (x : Spacetime) :
    superpotential h ρ μ ν x = -superpotential h ρ ν μ x := by
  sorry
end TeleparallelGravity
