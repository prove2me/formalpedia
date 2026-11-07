-- Prove2me | Theorems.Thm_SteinerAPX_tubes_disjoint
-- name    : SteinerAPX.tubes_disjoint
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:07.876231+00:00
-- url     : https://prove2.me/theorems/28c35e00-d722-4374-990e-429ab44d1239
-- title:
--   §4.2, pp.14–15 — the tubes of radius $\rho$ around middle segments are pairwise disjoint
-- statement:
--   Let a well-formed, separated cable layout of a 3DM-3 instance in $\mathbb R^D$ be given and $0<\rho\le1/100$. For every cable segment $e$ choose a middle segment $(a_e,b_e)$ and let $Z_e$ be the tube of radius $\rho$ around it. Then for any two distinct cable segments $e\neq e'$ (on the same or on different cables) and any such choices,
--   $$
--   Z_e\cap Z_{e'}=\emptyset .
--   $$
--   For segments on different cables, or non-incident segments of one cable, the segments are more than $2\rho$ apart; for incident segments the $45^\circ$ angle of (S2) keeps the middle segment of one at distance more than $7\rho$ from the other.
--
--   Disjointness lets the cable-recovery lemma sum the lengths of a tree inside the tubes: $\sum_e w_e\le\operatorname{len}(T)$.
--
--   Differences from the source:
--   - generalization: b₁, b₂ two orthogonal unit coordinate vectors of ℝᴰ → b₁, b₂ any orthonormal pair (CableLayout.WellFormed) in any EuclideanSpace ℝ ι; reason: a linear isometry of ℝᴰ maps any orthonormal pair onto two coordinate vectors and preserves every quantity in the statement, so the statement specializes to the source's coordinate vectors
--   - encoding: a 3DM-3 instance H with three parts of size r → an Inst3DM, whose parts have size r ≥ 1; reason: excludes only the empty instance (no elements, no triples, no gadgets), which the paper never considers (it assumes 4r ≤ m, §2)
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), §4.2, pp.14–15 (PDF pp.16–17)

import Mathlib
import Definitions.Def_SteinerAPX_Separated
import Definitions.Def_SteinerAPX_tube

namespace SteinerAPX

open Inst3DM CableLayout

/-- **The tubes are pairwise disjoint.** S. Bartlmae, *Inapproximability of Euclidean Steiner
Tree*, STOC 2027 submission (manuscript sha256 6f78a9ea…), §4.2, pp.14–15 (PDF pp.16–17): "These
tubes are pairwise disjoint: for segments on different cables or non-incident segments on the same
cable, this follows because their distance exceeds 2ρ. If segments e, e′ share an endpoint p, their
angle is at least 45° by (S2), so every point on the middle segment of e′ is at least 10ρ from p
and hence at least 10ρ sin 45° > 7ρ from e. The tube of e′ therefore has distance greater than 6ρ
from e, so the two tubes are disjoint."

For a well-formed, separated layout of a 3DM-3 instance in `ℝᴰ` and `0 < ρ ≤ 1/100`: for any two
distinct cable segments `e ∈ Γᵢ`, `e' ∈ Γⱼ` and any choices of middle segments `(a, b)` of `e` and
`(a', b')` of `e'`, the tubes of radius `ρ` around `[a, b]` and `[a', b']` are disjoint.

**Formalization Note** All three cases of the paragraph (different cables, non-incident and
incident segments of one cable) are covered. A segment is identified by its cable and its endpoint
pair. -/
theorem tubes_disjoint {ι : Type} [Fintype ι] (H : Inst3DM)
    (L : CableLayout H (EuclideanSpace ℝ ι)) (hH : H.IsThreeDM3) (hL : L.WellFormed)
    (hsep : Separated L) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 100) :
    ∀ i j : Label H, ∀ e ∈ L.cable i, ∀ e' ∈ L.cable j, (i, e) ≠ (j, e') →
      ∀ a b a' b' : EuclideanSpace ℝ ι, IsMiddle ρ e.1 e.2 a b → IsMiddle ρ e'.1 e'.2 a' b' →
        Disjoint (tube a b ρ) (tube a' b' ρ) := by sorry

end SteinerAPX
