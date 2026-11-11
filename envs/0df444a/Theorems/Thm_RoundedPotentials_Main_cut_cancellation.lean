-- Prove2me | Theorems.Thm_RoundedPotentials_Main_cut_cancellation
-- name    : RoundedPotentials.Main.cut_cancellation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T08:33:58.77069+00:00
-- url     : https://prove2.me/theorems/5d7f0c03-0222-402c-ae4a-558fc96d8dcf
-- title:
--   §2, eq. (3) — cut cancellation
-- statement:
--   For every real assignment $f$ on all ordered vertex pairs and every vertex set $S$,
--   $$\sum_{v\in S}\operatorname{ex}_f(v)=\sum_{u\in S,v\notin S}f_{uv}-\sum_{u\notin S,v\in S}f_{uv}.$$
--   No feasibility or conservation is assumed. This identity relates local excess checks to cut bounds, including for the empty set and empty vertex type.
--
--   Differences from the source:
--   - encoding: a finite vertex set V of size n → vertices Fin n and a finite vertex subset S; reason: relabeling preserves every assignment, vertex subset and crossing sum; the identity imposes no edge-list or feasibility hypothesis
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 12, §2, eq. (3)

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Certificate

namespace RoundedPotentials.Main
open scoped BigOperators

theorem cut_cancellation {n : ℕ} (f : Assignment n) (S : Finset (Fin n)) :
    (∑ v ∈ S, excess f v) =
      (∑ u ∈ S, ∑ v ∈ Sᶜ, f u v) - (∑ u ∈ Sᶜ, ∑ v ∈ S, f u v) := by sorry

end RoundedPotentials.Main
