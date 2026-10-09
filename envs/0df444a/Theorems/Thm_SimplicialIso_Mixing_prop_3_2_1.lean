-- Prove2me | Theorems.Thm_SimplicialIso_Mixing_prop_3_2_1
-- name    : SimplicialIso.Mixing.prop_3_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:13.502813+00:00
-- url     : https://prove2.me/theorems/f3c1551a-6056-46c0-a683-4eec65dc4d05
-- title:
--   Proposition 3.2 (1), (3.4), p. 9 — the upper Laplacian of the complement complex is Δ⁺_{X̄} = n·I − Δ_X
-- statement:
--   Let $X$ be a $d$-dimensional complex with a complete skeleton on $n$ vertices, $d\ge1$, and let $\overline X$ be its complement complex: the same complete skeleton, with $\overline X^d=\binom{V}{d+1}\setminus X^d$. Then
--   $$\Delta^+_{\overline X}=n\cdot I-\Delta_X,\qquad (3.4)$$
--   where $\Delta_X=\Delta^+_X+\Delta^-_X$ is the full Laplacian of $X$.
--
--   In the proof of the Mixing Lemma this identity converts $\langle\varphi,\Delta^-\psi\rangle$ into a count of $d$-cells of $X$ and of $\overline X$, which together are all $(d+1)$-sets.
--
--   **Formalization Note.** The identity is an equality of linear maps on $\Omega^{d-1}$; $\Delta^-$ depends only on the (complete) skeleton and is the same for $X$ and $\overline X$.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, p. 9, Proposition 3.2 (1), equation (3.4)

import Mathlib
import Definitions.Def_SimplicialIso_Mixing_Setting

namespace SimplicialIso.Mixing

open Finset
open scoped InnerProductSpace

/-- Proposition 3.2 (1), (3.4), p. 9: `Δ⁺_{X̄} = n · I − Δ_X` for the complement complex. -/
theorem prop_3_2_1 (n d : ℕ) (hd : 1 ≤ d) (X : Complex n d) :
    upLap X.compl = (n : ℝ) • LinearMap.id - fullLap X := by sorry

end SimplicialIso.Mixing
