-- Prove2me | Theorems.Thm_SimplicialIso_Mixing_exact_eq_orthogonal_cycles
-- name    : SimplicialIso.Mixing.exact_eq_orthogonal_cycles
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:24:07.070001+00:00
-- url     : https://prove2.me/theorems/87662094-5279-4a30-8a69-19971dfc5694
-- title:
--   p. 6 — the exact forms are the orthogonal complement of the cycles, B^{d−1} = im ∂*_{d−1} = Z_{d−1}^⊥
-- statement:
--   Let $d\ge1$ and $n\ge0$. In $\Omega^{d-1}$ with the inner product (2.1), the space of exact forms is the orthogonal complement of the space of $(d-1)$-cycles:
--   $$B^{d-1}=\operatorname{im}\partial^*_{d-1}=Z_{d-1}^{\perp}.$$
--
--   This gives the orthogonal decomposition $\Omega^{d-1}=B^{d-1}\oplus Z_{d-1}$ used in (4.8).
--
--   **Formalization Note.** Both $\partial_{d-1}$ and $\partial^*_{d-1}$ are defined by their formulas on the complete skeleton, so this statement includes the fact that $\partial^*_{d-1}$ is the adjoint of $\partial_{d-1}$. $d\ge1$ is the standing assumption of the mission.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, p. 6, 'B^j = im ∂*_j = Z_j^⊥ exact j-forms', case j = d − 1

import Mathlib
import Definitions.Def_SimplicialIso_Mixing_Setting

namespace SimplicialIso.Mixing

open Finset
open scoped InnerProductSpace

/-- p. 6: `B^{d-1} = im ∂*_{d-1} = Z_{d-1}^⊥`. -/
theorem exact_eq_orthogonal_cycles (n d : ℕ) (hd : 1 ≤ d) :
    exact n d = (cycles n d)ᗮ := by sorry

end SimplicialIso.Mixing
