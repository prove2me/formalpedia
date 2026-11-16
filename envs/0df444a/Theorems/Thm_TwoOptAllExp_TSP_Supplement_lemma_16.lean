-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_Supplement_lemma_16
-- name    : TwoOptAllExp.TSP.Supplement.lemma_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T04:46:48.751445+00:00
-- url     : https://prove2.me/theorems/84229a9f-5831-4e14-963f-fa6d7d8b6743
-- title:
--   Lemma 16 — following a literal: exact criteria for $x\leftarrow y$ and $x\leftarrow\bar y$
-- statement:
--   In a weighted graph objective, let $x$ have neighbor $y$ and let $B=B_x(y)=\sum_{ux\in E,u\ne y}|w(xu)|$. Then
--
--   1. $x\leftarrow y$ holds if and only if $b_x-w(xy)-B>0$ and $b_x+w(xy)+B<0$;
--   2. $x\leftarrow\bar y$ holds if and only if $b_x+w(xy)-B>0$ and $b_x-w(xy)+B<0$;
--   3. if $b_x=0$, then $x\leftarrow y$ iff $w(xy)<-B$, and $x\leftarrow\bar y$ iff $w(xy)>B$.
--
--   Here following is required over all assignments. These criteria certify most of the gadget relations of Lemma 19.
--
--   Differences from the source: none.
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Lemma 16, pp. 25–26

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_GraphObjective

namespace TwoOptAllExp.TSP.Supplement

/-- **Lemma 16** (Following a literal, pp. 25–26). Let `x` have neighbor `y` and `B = B_x(y)`.
(a) `x ← y` iff `b_x - w(xy) - B > 0` and `b_x + w(xy) + B < 0`;
(b) `x ← ȳ` iff `b_x + w(xy) - B > 0` and `b_x - w(xy) + B < 0`.
In particular, if `b_x = 0`, then `x ← y` iff `w(xy) < -B`, and `x ← ȳ` iff `w(xy) > B`. -/
theorem lemma_16 {V : Type} [Fintype V] [DecidableEq V] (W : WGraph V) (x y : V)
    (hxy : W.G.Adj x y) :
    (W.Follows x (fun σ => σ y) ↔
      0 < W.b x - W.w s(x, y) - W.B x y ∧ W.b x + W.w s(x, y) + W.B x y < 0) ∧
    (W.Follows x (fun σ => !σ y) ↔
      0 < W.b x + W.w s(x, y) - W.B x y ∧ W.b x - W.w s(x, y) + W.B x y < 0) ∧
    (W.b x = 0 →
      (W.Follows x (fun σ => σ y) ↔ W.w s(x, y) < -W.B x y) ∧
      (W.Follows x (fun σ => !σ y) ↔ W.B x y < W.w s(x, y))) := by sorry

end TwoOptAllExp.TSP.Supplement
