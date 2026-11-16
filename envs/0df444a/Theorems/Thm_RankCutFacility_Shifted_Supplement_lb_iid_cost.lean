-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_Supplement_lb_iid_cost
-- name    : RankCutFacility.Shifted.Supplement.lb_iid_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:23:27.916172+00:00
-- url     : https://prove2.me/theorems/18ad6d8f-190f-40c5-882f-9ae459e422d1
-- title:
--   Lemma 6.5 — $\mathbb E[\mathrm{ALG}]\ge N$ under i.i.d. demand
-- statement:
--   On the unit-cost prescribed-candidate instance of Section 6.1 with $N\ge2$, draw the $N$ demand points independently and uniformly from $X$.
--
--   **Lemma 6.5.** Every randomized online algorithm has expected cost at least $N$ under this i.i.d. demand distribution:
--
--   $$\mathbb E[\mathrm{ALG}]\ge N.$$
--
--   Combined with $\mathrm{OPT}=1+N/3$ (Lemma 6.3) and the conditioning on the drawn multiset, this gives Theorem 6.1.
--
--   Differences from the source:
--   - encoding: a randomized online algorithm (knowing the metric, costs, horizon and demand distribution, possibly opening several facilities per round) → a probability mass function over deterministic online algorithms, each a map from the revealed request prefix to the finite set of candidates opened in that round, independent of the demand randomness; reason: on a fixed finite instance with fixed horizon only finitely many deterministic behaviours exist, so every randomized algorithm is such a mixture; the public data are fixed before the algorithm is chosen
--   - encoding: N independent uniform draws from X → the uniform average over all maps Fin N → Fin m; reason: this is the product uniform law on a finite set
--   - encoding: real costs with d(x, ∅) = +∞ → costs in [0, ∞] (ENNReal), with d(x, ∅) = ⊤; reason: an algorithm that leaves the open set empty in some round pays +∞, exactly as in the source
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf, Lemma 6.5, printed p. 20 (PDF p. 22)

import Definitions.Def_RankCutFacility_Shifted_Supplement_Online

noncomputable section
open scoped ENNReal

namespace RankCutFacility.Shifted.Supplement

/-- Lemma 6.5 (PDF p. 22, printed p. 20): in the i.i.d. experiment on the unit-cost
prescribed-candidate instance of Section 6.1, every randomized online algorithm has
`E[ALG] ≥ N`. -/
theorem lb_iid_cost (N : ℕ) (hN : 2 ≤ N) (ρ : PMF (OnlineAlg (LBFac N) (LBPoint N))) :
    (N : ℝ≥0∞) ≤
      iidExpected ρ (fun A w => onlineCost (lbDist N) (lbSite N) (lbUnitFee N) A (lbDemand w)) := by sorry

end RankCutFacility.Shifted.Supplement
