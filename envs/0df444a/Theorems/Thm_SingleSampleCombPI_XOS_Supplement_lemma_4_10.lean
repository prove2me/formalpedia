-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_lemma_4_10
-- name    : SingleSampleCombPI.XOS.Supplement.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:45:20.452333+00:00
-- url     : https://prove2.me/theorems/7d31e9dc-d7ee-4fa9-ad33-1e1998fd078d
-- title:
--   Lemma 4.10 — Primal increment dominates gamma times the dual increment
-- statement:
--   At every reachable Algorithm 6 state and every next valid DR-submodular concave valuation, each allocation satisfying Condition 1 gives
--   $$\mathrm{FD}(H')-\mathrm{FD}(H)\ge\gamma\bigl(\beta_i+\sum_j\alpha'_j-\sum_j\alpha_j\bigr).$$
--   Here $H'$ appends the new allocation with its canonical supporting prices, $\beta_i=v_i(x_i)-\langle x_i,\alpha'\rangle$, and $\gamma=1-e^{-1}$. The primal and dual quantities are defined independently of the inequality; no reverse-duality invariant is assumed.
--
--   Differences from the source:
--   - encoding: twice-differentiable DR-submodular concave valuations on the nonnegative orthant and Algorithm 6 → within-orthant first/second Frechet derivatives, antitone gradient, canonical Aumann–Shapley prices and reachable frozen-history transitions; reason: these are Definition 6 and Proposition 2.2 conventions; C² regularity, Lipschitz constants and arbitrary supplied supporting maps are not assumed
--   - encoding: valid states, traces and arbitrary arrival order → inductively reachable histories and explicit order-indexed frozen records; reason: only initialization and actual Condition 1 transitions are assumed; no lemma conclusion or unproved algorithmic invariant is a state field
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Lemma 4.10, printed p. 25 / PDF p. 27; proof printed 25–26 / PDF 27–28.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_GreedyDR

namespace SingleSampleCombPI.XOS.Supplement

/-- Lemma 4.10, PDF 27 / printed 25. Primal increment versus the
new buyer's beta plus the increase in the alpha objective. -/
theorem lemma_4_10 {m : ℕ} (H : FrozenHistory m) (hH : A6Reachable H)
    (v : Vec m → ℝ) (hv : DRConcave v) (x : Cube m) (hx : condition1 H v x) :
    let H' := H ++ [freeze (drBuyer v) x]
    gamma * (v x.1 - dot (a6Alpha H') x.1 +
      (∑ j, a6Alpha H' j) - (∑ j, a6Alpha H j)) ≤ historyFD H' - historyFD H := by sorry

end SingleSampleCombPI.XOS.Supplement
