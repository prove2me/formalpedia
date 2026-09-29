-- Prove2me | Theorems.Thm_Verlinde2016_principal_strain_bound
-- name    : Verlinde2016.principal_strain_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T22:30:15.886775+00:00
-- url     : https://prove2.me/theorems/006fb60f-bff0-4c79-97f4-1602bfea23ed
-- title:
--   Eq. (7.30) — bound on the largest principal strain of a deviatoric strain tensor
-- statement:
--   Let $d\ge2$ be the spacetime dimension, so space has dimension $d-1$. Let $\varepsilon'_{ij}$ be a real symmetric, traceless $(d-1)\times(d-1)$ matrix (a deviatoric strain tensor), and let $\varepsilon$ be a principal strain, i.e. an eigenvalue of $\varepsilon'$ with eigenvector $n\neq0$: $\varepsilon'_{ij}n_j = \varepsilon n_i$. Then
--   $$\varepsilon^2 \le \left(\frac{d-2}{d-1}\right)\varepsilon'^{\,2}_{ij},\qquad \varepsilon'^{\,2}_{ij} = \sum_{i,j}(\varepsilon'_{ij})^2.$$
--   The paper states this for the largest principal strain; the bound holds for every eigenvalue, which is what is formalized.
-- source:
--   E. Verlinde, Emergent Gravity and the Dark Universe, SciPost Phys. 2, 016 (2017), arXiv:1611.02269v2, https://arxiv.org/abs/1611.02269, p. 35, eq. (7.30) (with (7.28) for the eigenvector condition)

import Mathlib
import Definitions.Def_Verlinde2016_Defs

open Real

namespace Verlinde2016

theorem principal_strain_bound (d : ℕ) (hd : 2 ≤ d)
    (E : Matrix (Fin (d - 1)) (Fin (d - 1)) ℝ) (hE : E.IsSymm) (htr : E.trace = 0)
    (ε : ℝ) (v : Fin (d - 1) → ℝ) (hv : v ≠ 0) (hev : E.mulVec v = ε • v) :
    ε ^ 2 ≤ ((d : ℝ) - 2) / ((d : ℝ) - 1) * ∑ i, ∑ j, E i j ^ 2 := by sorry

end Verlinde2016
