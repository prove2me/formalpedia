-- Prove2me | Theorems.Thm_PolygonPack_lemma_B_1
-- name    : PolygonPack.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:57.359814+00:00
-- url     : https://prove2.me/theorems/0b3fadd6-9d92-4532-959f-827975a344af
-- title:
--   Lemma B.1 — seven comparison tracks
-- statement:
--   Let $0<c\le1/400$, $t_0\le1/1000$, $a_0>0$, and let $h_0=2a_0$ satisfy
--   $$
--   h_0\le\min\{c/400,\ 1/(500K),\ 1/(300LK),\ 1/(82M),\ 1/16\}.
--   $$
--   Let $F$ be a feasible family of a valid instance whose polygons are positive-Tight or Slack, with job data $(d_i,p_i)$ and $d_i+p_i\le t_0$. Then $F$ has a seven-track schedule.
--
--   The data of a positive-Tight polygon may use any of its canonical poses. This schedule is what certifies a profitable track among the input jobs.
--
--   Differences from the source:
--   - encoding: positive-Tight jobs, with data from "any maximizing pose" → (d, p) from any canonical pose, per polygon; reason: the paper allows any maximizer on p.22 and p.47
--   - reading: early jobs → d + p ≤ t0; reason: the preamble of App. B: completion deadline at most t0
--   - reading: a cutoff h0 → h0 = 2·a0 with a0 > 0 in the classes; reason: p.20
--   - generalization: convex polygons given by their vertices → the convex hull of any finite rational vertex list, in any order; reason: the vertices of a convex polygon are such a list
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Lemma B.1, p.29 (eq. (11)); early jobs, App. B preamble, p.29

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
import Definitions.Def_PolygonPack_IsTrackSchedule

namespace PolygonPack

/-- **Lemma B.1 (Seven comparison tracks).** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), p.29. "Let c ≤ 1/400 and t0 ≤ 1/1000. With K = 2/c + 1 and L = 2/c + 6 from Lemma A.2 and M = 339/c + 6 from
Lemma A.3, take h0 ≤ min{c/400, 1/(500K), 1/(300LK), 1/(82M), 1/16}. (11) Every feasible family of positive-Tight and Slack early jobs has a seven-track
schedule, as claimed in Lemma 2.3."

Here `h0 = 2·a0`. "Early" is the App. B preamble, p.29: the completion deadline `Δ = d + p` is at most `t0`.

**Formalization Note.** The job data of a positive-Tight polygon use any canonical pose (`IsJobData`), since `p` depends on the maximizer. A job with `Δ > t0`
is outside the family. -/
theorem lemma_B_1 (c a0 t0 : ℝ) (hc : 0 < c) (hc' : c ≤ 1 / 400) (ht0 : t0 ≤ 1 / 1000) (ha0 : 0 < a0)
    (hcut : IsB1Cutoff c (2 * a0)) (I : Instance) (hI : I.Valid) (F : Finset (Fin I.n)) (hF : Feasible I F)
    (d p : Fin I.n → ℝ) (hjob : ∀ i ∈ F, IsJobData c a0 (I.verts i) (d i) (p i) ∧ d i + p i ≤ t0) :
    IsTrackSchedule d p F 7 := by sorry

end PolygonPack
