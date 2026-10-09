-- Prove2me | Theorems.Thm_SimplicialIso_Mixing_eq_4_5
-- name    : SimplicialIso.Mixing.eq_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:23:50.673208+00:00
-- url     : https://prove2.me/theorems/c2c1191f-4dcd-41df-8852-d0a1e4a03970
-- title:
--   (4.5), p. 17 — for disjoint B_0,…,B_{d−1}, ‖δ_{B_0,…,B_{d−1}}‖ = √(|B_0|⋯|B_{d−1}|)
-- statement:
--   Let $d\ge1$ and let $B_0,\dots,B_{d-1}$ be pairwise disjoint sets of vertices among $n$. Since the skeleton is complete, the form $\delta_{B_0,\dots,B_{d-1}}$ has norm
--   $$\|\delta_{B_0,\dots,B_{d-1}}\|=\sqrt{\sum_{\sigma\in X^{d-1}}\delta^2_{B_0,\dots,B_{d-1}}(\sigma)}=\sqrt{|B_0|\cdots|B_{d-1}|}.\qquad(4.5)$$
--
--   It bounds $\|\varphi\|\cdot\|\psi\|$ in (4.11).
--
--   **Formalization Note.** The norm is the `EuclideanSpace` norm, i.e. the one induced by (2.1). Some blocks may be empty; then both sides are $0$.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, §4.3, p. 17, equation (4.5)

import Mathlib
import Definitions.Def_SimplicialIso_Mixing_Setting
import Definitions.Def_SimplicialIso_Mixing_DeltaForms

namespace SimplicialIso.Mixing

open Finset
open scoped InnerProductSpace

/-- (4.5), p. 17: for disjoint `B_0, …, B_{d-1}`,
`‖δ_{B_0, …, B_{d-1}}‖ = √(|B_0| ⋯ |B_{d-1}|)`. -/
theorem eq_4_5 (n d : ℕ) (hd : 1 ≤ d) (B : Fin d → Finset (Fin n))
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) :
    ‖delta B‖ = Real.sqrt (∏ i, ((B i).card : ℝ)) := by sorry

end SimplicialIso.Mixing
