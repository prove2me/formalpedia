-- Prove2me | Theorems.Thm_PolygonPack_lemma_A_3
-- name    : PolygonPack.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:02.796209+00:00
-- url     : https://prove2.me/theorems/f6772ad0-72ca-4dce-be9e-112bf257dacb
-- title:
--   Lemma A.3 — canonical section and transfer
-- statement:
--   Let $P$ be a polygon of positive area with a diameter segment of length $D>1$, thickness $h$ and $\gamma=\sqrt{D^2-1}$. Suppose $h>c\delta$ for some $c>0$, the canonical bottom $d$ is positive, and $h\le\min\{c/16,\,1/16,\,1/(8K)\}$. Let $p$ be the vertical span of any canonical pose and $w_{\mathrm{can}}(0)$ its central section. Then
--   $$
--   w_{\mathrm{can}}(0)\ge\Bigl(\frac{\gamma}{1+\gamma}-Lh\Bigr)p,
--   $$
--   and every placement in the square whose diameter follows the chosen diagonal has central section $w_P(0)$ with
--   $$
--   |w_P(0)-w_{\mathrm{can}}(0)|\le98h\delta,\qquad w_P(0)\ge\Bigl(\frac12-Mh\Bigr)p,\qquad M=\frac{339}c+6 .
--   $$
--   This is the comparison that lets the vertical span of a canonical pose be charged to central sections in any feasible packing.
--
--   Differences from the source:
--   - generalization: P in T+ → h > cδ and d > 0, with no area condition; reason: membership in T+ implies these
--   - generalization: the fixed diameter segment of P → every diameter segment AB; reason: the fixed one is one of them
--   - generalization: convex polygons given by their vertices → the convex hull of any finite rational vertex list, in any order; reason: the vertices of a convex polygon are such a list
--   - encoding: first rotate the entire packing so that its diagonal is the u-diagonal; the section is measured after this → each placement has 0 ≤ X·Y for its diameter; reason: the rotated placement is such a placement
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Lemma A.3, p.23 (eqs. (5), (6))

import Mathlib
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_PolygonPack_Packs
import Definitions.Def_PolygonPack_Instance_Valid
import Definitions.Def_PolygonPack_diag
import Definitions.Def_PolygonPack_eucl
import Definitions.Def_PolygonPack_thick
import Definitions.Def_PolygonPack_diamPair
import Definitions.Def_PolygonPack_polyArea
import Definitions.Def_PolygonPack_placedUV
import Definitions.Def_PolygonPack_canonBottom
import Definitions.Def_PolygonPack_IsTight
import Definitions.Def_PolygonPack_Kc

namespace PolygonPack

/-- **Lemma A.3 (Canonical section and transfer).** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), p.23. "Suppose P ∈ T+ and h ≤ min{c/16, 1/16, 1/(8K)}. In its canonical pose
and in every feasible placement following the chosen diagonal, respectively, w_can(0) ≥ (γ/(1 + γ) − Lh)p, (5)
|w_P(0) − w_can(0)| ≤ 98hδ. (6) In particular, w_P(0) ≥ (1/2 − Mh)p, where M = 339/c + 6."

For every diameter segment `AB` with `D > 1` and `h > cδ`, positive canonical bottom, and every canonical pose `T0`
(`p` is its vertical span). The last two conclusions hold for every placement `T` following the chosen diagonal.

**Formalization Note.** Membership in `T+` is used through `h > cδ` and `d > 0` only, so there is no area condition. The next
sentence of the lemma says a comparison packing is first rotated so that its diagonal is the `u`-diagonal. The Lean states the
placement with `0 ≤ X·Y` directly. -/
theorem lemma_A_3 (c : ℝ) (hc : 0 < c) (v : List (ℚ × ℚ)) (A B : ℚ × ℚ) (hpos : PosArea v) (hd : IsDiameterSeg v A B)
    (hD : 1 < lenD A B) (hTight : c * deficit (lenD A B) < thick v A B) (hd0 : 0 < canonBottom v A B)
    (hh : thick v A B ≤ c / 16 ∧ thick v A B ≤ 1 / 16 ∧ thick v A B ≤ 1 / (8 * Kc c))
    (T0 : Pose) (hcan : IsCanonicalPose v A B T0) :
    (gam (lenD A B) / (1 + gam (lenD A B)) - Lc c * thick v A B) * vSpan (placedUV v T0) ≤ wSec (placedUV v T0) 0 ∧
    ∀ T : Pose, IsPlacement v T → ChosenDiag A B T →
      |wSec (placedUV v T) 0 - wSec (placedUV v T0) 0| ≤ 98 * thick v A B * deficit (lenD A B) ∧
      (1 / 2 - Mc c * thick v A B) * vSpan (placedUV v T0) ≤ wSec (placedUV v T) 0 := by sorry

end PolygonPack
