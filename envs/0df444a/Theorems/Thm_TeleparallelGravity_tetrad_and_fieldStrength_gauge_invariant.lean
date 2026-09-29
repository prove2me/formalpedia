-- Prove2me | Theorems.Thm_TeleparallelGravity_tetrad_and_fieldStrength_gauge_invariant
-- name    : TeleparallelGravity.tetrad_and_fieldStrength_gauge_invariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T22:32:16.706813+00:00
-- url     : https://prove2.me/theorems/1ef5e9bc-aac1-4899-9163-323856c67b5d
-- title:
--   Gauge invariance of the tetrad and of $F^a{}_{\mu\nu}$ under local translations (Eqs. (2)-(3))
-- statement:
--   Let $x^a$, $\varepsilon^a$ ($a=0,\dots,3$) and $B^a{}_\mu$ be smooth real functions on $\mathbb R^4$. Under the local translation $x^a\mapsto x^a+\varepsilon^a$ with the gauge transformation $B^a{}_\mu\mapsto B'^a{}_\mu=B^a{}_\mu-\partial_\mu\varepsilon^a$ (Eq. (2)), the tetrad $h^a{}_\mu=\partial_\mu x^a+B^a{}_\mu$ (Eq. (3)) is unchanged, and so is the field strength: $F'^a{}_{\mu\nu}=\partial_\mu B'^a{}_\nu-\partial_\nu B'^a{}_\mu=F^a{}_{\mu\nu}$ for all indices and all points.
-- source:
--   R. Aldrovandi, J. G. Pereira, K. H. Vu, "Selected Topics in Teleparallel Gravity", Brazilian Journal of Physics 34 (2004), no. 4A, 1374-1380, https://doi.org/10.1590/S0103-97332004000700009 — Gauge invariance of the tetrad and of $F^a{}_{\mu\nu}$ under local translations (Eqs. (2)-(3))

import Mathlib
import Definitions.Def_TeleparallelGravity_Defs

open scoped ContDiff

namespace TeleparallelGravity
theorem tetrad_and_fieldStrength_gauge_invariant
    (xa ε : Fin 4 → Spacetime → ℝ) (B : TetradField)
    (hxa : ∀ a, ContDiff ℝ ∞ (xa a)) (hε : ∀ a, ContDiff ℝ ∞ (ε a))
    (hB : ∀ a μ, ContDiff ℝ ∞ (B a μ)) :
    tetradOfPotential (fun a y => xa a y + ε a y) (fun a μ y => B a μ y - pd μ (ε a) y)
        = tetradOfPotential xa B ∧
      fieldStrength (fun a μ y => B a μ y - pd μ (ε a) y) = fieldStrength B := by
  sorry
end TeleparallelGravity
