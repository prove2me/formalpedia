-- Prove2me | Theorems.Thm_SimplicialIso_Mixing_prop_3_2_3
-- name    : SimplicialIso.Mixing.prop_3_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:18.728985+00:00
-- url     : https://prove2.me/theorems/bd5ac5bd-37da-4c0a-beee-648ba08110cb
-- title:
--   Proposition 3.2 (3), (3.5), p. 9 — the lower Laplacian is Δ⁻ = n·ℙ_{B^{d−1}}
-- statement:
--   Let $d\ge1$. On a complex with a complete skeleton on $n$ vertices the lower Laplacian $\Delta^-=\partial^*_{d-1}\partial_{d-1}$ on $\Omega^{d-1}$ is $n$ times the orthogonal projection onto the exact forms:
--   $$\Delta^-=n\cdot\mathbb P_{B^{d-1}}.\qquad (3.5)$$
--
--   With (3.4) this identifies $\langle\varphi,\mathbb P_{B^{d-1}}\psi\rangle$ in the proof of the Mixing Lemma.
--
--   **Formalization Note.** Stated pointwise: $\Delta^- f=n\,\mathbb P_{B^{d-1}}f$ for every $f\in\Omega^{d-1}$. $\Delta^-$ does not depend on the $d$-cells, so no complex appears.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, p. 9, Proposition 3.2 (3), equation (3.5)

import Mathlib
import Definitions.Def_SimplicialIso_Mixing_Setting

namespace SimplicialIso.Mixing

open Finset
open scoped InnerProductSpace

/-- Proposition 3.2 (3), (3.5), p. 9: `Δ⁻ = n · ℙ_{B^{d-1}}`. -/
theorem prop_3_2_3 (n d : ℕ) (hd : 1 ≤ d) (f : Form n d) :
    lowLap n d f = (n : ℝ) • projExact n d f := by sorry

end SimplicialIso.Mixing
