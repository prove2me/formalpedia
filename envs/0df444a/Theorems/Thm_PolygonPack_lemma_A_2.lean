-- Prove2me | Theorems.Thm_PolygonPack_lemma_A_2
-- name    : PolygonPack.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:01.133049+00:00
-- url     : https://prove2.me/theorems/78d66ed0-6b64-4e8c-bbf8-2798fae53b26
-- title:
--   Lemma A.2 — sections near the center
-- statement:
--   Let $P$ be a polygon of positive area with a diameter segment $AB$ of length $D>1$, thickness $h$, and $\delta=\sqrt2-D\le1/16$, placed in the unit square so that $AB$ follows the chosen diagonal. Let $[f(u),g(u)]$ be its vertical sections in diagonal coordinates, $w=g-f$, and $\gamma=\sqrt{D^2-1}$. Then $f,g$ have Lipschitz constant at most $2\delta+4\sqrt2h$ on $I=[-1/4,1/4]$, and
--   $$
--   w(0)\ge\frac{\gamma}{1+\gamma}h\ge\frac h3 .
--   $$
--   If moreover $c>0$ and $h>c\delta$, then $|v|\le Kh$ throughout $P$ and $f,g$ have Lipschitz constant at most $Lh$ on $I$, where $K=2/c+1$ and $L=2/c+6$.
--
--   The lemma says that a long polygon has slowly varying section boundaries near the centre, with a central section comparable to its thickness.
--
--   Differences from the source:
--   - generalization: P additionally Tight → c > 0 and h > cδ, with no area condition; reason: Tight implies these
--   - generalization: the fixed diameter segment of P → every diameter segment AB; reason: the fixed one is one of them
--   - generalization: convex polygons given by their vertices → the convex hull of any finite rational vertex list, in any order; reason: the vertices of a convex polygon are such a list
--   - encoding: Lipschitz constant at most C on I → |f(x) − f(y)| ≤ C|x − y| for x, y in I; reason: the same condition
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Lemma A.2, p.22 (eq. (4))

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

/-- **Lemma A.2 (Sections near the center).** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), p.22. "If δ ≤ 1/16, both boundaries on I = [−1/4, 1/4] have Lipschitz
constant at most 2δ + 4√2h, and w(0) ≥ (γ/(1 + γ))h ≥ h/3, γ = √(D² − 1). (4) In particular, if P is additionally Tight, then
|v| ≤ Kh throughout P, Lip_I(f), Lip_I(g) ≤ Lh, K = 2/c + 1, L = 2/c + 6."

The polygon has positive area and diameter segment `AB` with `D > 1`, in a placement `T` in the square whose diameter follows
the chosen diagonal (the preamble of p.22).

**Formalization Note.** "Tight" is used through `h > cδ` with `c > 0` only, so the last clause has no area condition: it
covers the class `IsTight`. It holds for every diameter segment, not only the fixed one. -/
theorem lemma_A_2 (v : List (ℚ × ℚ)) (A B : ℚ × ℚ) (T : Pose) (hpos : PosArea v) (hd : IsDiameterSeg v A B)
    (hD : 1 < lenD A B) (hT : IsPlacement v T) (hC : ChosenDiag A B T) (hδ : deficit (lenD A B) ≤ 1 / 16) :
    IsLipOn (2 * deficit (lenD A B) + 4 * Real.sqrt 2 * thick v A B) (secLo (placedUV v T)) centralI ∧
    IsLipOn (2 * deficit (lenD A B) + 4 * Real.sqrt 2 * thick v A B) (secHi (placedUV v T)) centralI ∧
    gam (lenD A B) / (1 + gam (lenD A B)) * thick v A B ≤ wSec (placedUV v T) 0 ∧
    thick v A B / 3 ≤ gam (lenD A B) / (1 + gam (lenD A B)) * thick v A B ∧
    ∀ c : ℝ, 0 < c → c * deficit (lenD A B) < thick v A B →
      (∀ q ∈ placedUV v T, |q.2| ≤ Kc c * thick v A B) ∧
      IsLipOn (Lc c * thick v A B) (secLo (placedUV v T)) centralI ∧
      IsLipOn (Lc c * thick v A B) (secHi (placedUV v T)) centralI := by sorry

end PolygonPack
