-- Prove2me | Theorems.Thm_PrizeAlloc_Param_winner_prize_inverse
-- name    : PrizeAlloc.Param.winner_prize_inverse
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:52.933773+00:00
-- url     : https://prove2.me/theorems/607ee7d2-eb38-4514-a012-763443ea2418
-- title:
--   Proof of Theorem 3, pp. 32–33 — the winner's prize is an unbounded, continuous, increasing function of the endowment
-- statement:
--   Let $\varphi$ be a prize allocation rule satisfying order preservation, winner strict endowment monotonicity and endowment continuity, let $(N,\mathcal R)$ be a ranked set of competitors, and let $w\in N$ be the winner, $\mathcal R(w)=1$. Then the map $E\mapsto\varphi_w(N,\mathcal R,E)$ on $\mathbb R_+$ is
--
--   1. strictly increasing,
--   2. continuous,
--   3. unbounded above,
--
--   and consequently
--
--   $$\forall x\ge 0\quad \exists!\,E\ge 0:\ \varphi_w(N,\mathcal R,E)=x.$$
--
--   This inversion is what lets the proof of Theorem 3 parametrize every competition with $n+1$ competitors by the winner's prize $x$.
--
--   **Formalization Note** Endowment continuity is a hypothesis here, as in the sentence of the proof; in the paper it follows from endowment monotonicity by Lemma 1, which is formalized in a companion mission of this series. The standing hypotheses on $U$ are not used and are omitted.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, pp. 32–33, proof of Theorem 3, sentence beginning "By order preservation, endowment continuity, and winner strict endowment monotonicity"

import Mathlib
import Definitions.Def_PrizeAlloc_Param_Setting
import Definitions.Def_PrizeAlloc_Param_ParametricRule

namespace PrizeAlloc.Param

/-- Proof of Theorem 3, pp. 32–33: the winner's prize `E ↦ φ_1(N, R, E)` is an unbounded,
continuous, increasing function of `E ∈ ℝ₊`, so each `x ≥ 0` is the winner's prize for a
unique `E ≥ 0`. -/
theorem winner_prize_inverse {U : Type*} [DecidableEq U]
    (φ : List U → ℝ → U → ℝ) (hφ : PrizeAlloc.Interval.IsPrizeRule φ)
    (hOP : PrizeAlloc.Interval.OrderPreserving φ) (hWSM : PrizeAlloc.Interval.WinnerStrictMonotone φ) (hEC : PrizeAlloc.Interval.EndowmentContinuous φ)
    (l : List U) (hl : PrizeAlloc.Interval.IsRanking l) (w : U) (hw : w ∈ l) (hw1 : PrizeAlloc.Interval.pos l w = 1) :
    StrictMonoOn (fun E => φ l E w) (Set.Ici 0) ∧
      ContinuousOn (fun E => φ l E w) (Set.Ici 0) ∧
      ¬ BddAbove ((fun E => φ l E w) '' Set.Ici 0) ∧
      ∀ x : ℝ, 0 ≤ x → ∃! E : ℝ, 0 ≤ E ∧ φ l E w = x := by sorry

end PrizeAlloc.Param
