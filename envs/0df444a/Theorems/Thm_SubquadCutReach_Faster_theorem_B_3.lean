-- Prove2me | Theorems.Thm_SubquadCutReach_Faster_theorem_B_3
-- name    : SubquadCutReach.Faster.theorem_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:59:30.175809+00:00
-- url     : https://prove2.me/theorems/636b4af3-5d64-46b5-8358-ccc93962d3b0
-- title:
--   Theorem B.3 — Reserve partition
-- statement:
--   Let $J$ be a simple graph on $n$ vertices, put $k=n^{2/3}$, and let $F$ be the union of $\lceil10k\log n\rceil$ successive spanning forests of residual graphs. There is a partition $\mathcal P$ into nonempty induced vertex parts with
--
--   $$|C|=1\quad\text{or}\quad \min_{\varnothing\ne S\subsetneq C}|E_J(S,C\setminus S)|\ge k,$$
--
--   and every edge joining distinct parts belongs to $F$. The parts are not defined as connected components of $F$. The supplied forest sequence must satisfy exactly the successive residual spanning-forest property. This exposes the partition used in the simultaneous reserve estimate.
--
--   Differences from the source:
--   - encoding: labelled graphs and orientation rules → Fin n, Mathlib simple graphs and increasing-pair Boolean tables; reason: all finite labelled source graphs and all directions are represented; unused table cells carry no mathematical information
--   - encoding: 10k log n successive residual forests, k=n^(2/3) → ceil(10k log n) forests and a partition of induced vertex sets; reason: integer rounding defines the number of forests; the real cut threshold k is retained and no global connectivity hypothesis is added
--   - reading: 10k log n with the base of log unspecified → natural logarithm Real.log; reason: the base is not stated; the natural logarithm gives the fewer forests, so it is the stronger reading
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 25, Theorem B.3 (PDF p. 27)

import Definitions.Def_SubquadCutReach_Faster_Reserve

set_option autoImplicit false

namespace SubquadCutReach.Faster

theorem theorem_B_3 {n : ℕ} (J : SimpleGraph (Fin n))
    (Fs : ℕ → Finset (Fin n × Fin n)) (hF : ForestRun J Fs (forestRounds n)) :
    ∃ parts : Finset (Finset (Fin n)), StrongPartition J (forestUnion Fs (forestRounds n)) parts := by sorry

end SubquadCutReach.Faster
