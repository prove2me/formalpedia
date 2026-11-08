-- Prove2me | Theorems.Thm_PoSUndirected_eq_2_3_parameter_margins
-- name    : PoSUndirected.eq_2_3_parameter_margins
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:04.270194+00:00
-- url     : https://prove2.me/theorems/78b653f8-eeb5-4c67-8b94-0b0cb6e13215
-- title:
--   Equations (2)–(3) and the §A.5 margins hold strictly on the whole segment $0\le t<1$
-- statement:
--   For every rational $0\le t<1$ the parameter vector $\eta(t)=(1-t)\eta_0+t\eta_1$ satisfies:
--
--   1. $\alpha>0$, every nominal floor cost $a,\dots,k,L_y,L_z$ is positive, and every physical chord cost $x,\,y-L_y,\,z-L_z,\,u,\,v,\,w$ is positive;
--   2. equation (2), strictly:
--   $$
--   c_{\max}<\alpha,\qquad y-L_y>4L_y,\qquad z-L_z>4L_z,\qquad S_{\rm rec}>\alpha;
--   $$
--   3. equation (3):
--   $$
--   s_{\max}<49\alpha,\qquad s_{\max}/7<c_{\min};
--   $$
--   4. $S-\alpha>0$.
--
--   Here $c_{\max},c_{\min}$ range over the six physical chord costs and $s_{\max}$ over the thirteen nominal floors. These are the structural inequalities of the lower construction: (2) feeds the local comparison and the pendant contraction, (3) makes the floor tree the unique minimum spanning tree.
--
--   **Formalization Note** Each maximum and minimum is stated as the family of inequalities it abbreviates.
--
--   Differences from the source:
--   - generalization: equation (2) printed with $y-L_y\ge4L_y$, $z-L_z\ge4L_z$ → the strict inequalities; reason: the paper states that the parameters satisfy (2) strictly (p.14); the strict form implies the printed one
--   - generalization: positivity of the physical costs → also $\alpha>0$ and $S-\alpha>0$; reason: both are printed margins or standing assumptions of §A.5 (the "positive parameter $\alpha$", the margin $S-\alpha$); extra conclusions imply the printed ones
--   - encoding: $c_{\max}<\alpha$, $s_{\max}<49\alpha$, $s_{\max}/7<c_{\min}$ → the inequality for every chord, every floor and every pair; reason: the paper says each maximum or minimum abbreviates this family (p.20)
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), equation (2), p.14 (PDF p.16); equation (3), p.17 (PDF p.19); §A.5 margins, pp.19–20 (PDF pp.21–22)

import Mathlib
import Definitions.Def_PoSUndirected_Params

namespace PoSUndirected

open Params in
/-- Tsoufis (preprint, sha256 c095d811…), equations (2) (p.14 (PDF p.16)) and (3) (p.17
(PDF p.19)), with the positivity statement of §A.5 (p.20 (PDF p.22)), on the whole parameter
segment: for every rational `0 ≤ t < 1`, the point `η(t) = (1 − t)η₀ + tη₁` has `α > 0`, positive
nominal floor costs `a, …, k, L_y, L_z` and positive physical chord costs
`x, y − L_y, z − L_z, u, v, w`, and satisfies `c_max < α`, `y − L_y ≥ 4L_y`, `z − L_z ≥ 4L_z`,
`S_rec > α` (2) and `s_max < 49α`, `s_max/7 < c_min` (3), all strictly, where `c_max`, `c_min` range
over the six physical chord costs and `s_max` over the thirteen nominal floors, and the printed
margin `S − α > 0` (p.19 (PDF p.21)).

**Formalization Note.** Each maximum and minimum is written as the family of inequalities it
abbreviates (as the paper says on p.20). The paper prints `≥` in (2) and states that the
inequalities hold strictly; the strict form is stated. -/
theorem eq_2_3_parameter_margins (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < (etaAt t).α ∧ (∀ σ, 0 < (etaAt t).nominal σ) ∧ (∀ κ, 0 < (etaAt t).physChord κ) ∧
    (∀ κ, (etaAt t).physChord κ < (etaAt t).α) ∧
    4 * (etaAt t).Ly < (etaAt t).y - (etaAt t).Ly ∧ 4 * (etaAt t).Lz < (etaAt t).z - (etaAt t).Lz ∧
    (etaAt t).α < (etaAt t).Srec ∧ (∀ σ, (etaAt t).nominal σ < 49 * (etaAt t).α) ∧
    (∀ σ κ, (etaAt t).nominal σ / 7 < (etaAt t).physChord κ) ∧
    (etaAt t).α < (etaAt t).S := by sorry

end PoSUndirected
