-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_Supplement_general_lower_bound
-- name    : RankCutFacility.Shifted.Supplement.general_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:24:00.237212+00:00
-- url     : https://prove2.me/theorems/cc266e99-7492-4791-b795-76dccd79b326
-- title:
--   Theorem 6.1 — $3N/(N+3)$ lower bound with unit costs on prescribed candidates
-- statement:
--   Use the instance of Section 6.1: the metric of Lemma 6.2 on $X\cup Y$, candidate set $Y$, every opening cost one, horizon $N$ known to the algorithm.
--
--   **Theorem 6.1.** For every integer $N\ge2$ and every randomized online algorithm there exists a demand-point multiset of size $N$ (indeed inside $X$) such that, under uniformly random arrival order,
--
--   $$\frac{\mathbb E[\mathrm{ALG}]}{\mathrm{OPT}}\ge\frac{3N}{N+3}.$$
--
--   Letting $N\to\infty$ gives part (a) of Theorem 1.3: no randomized online algorithm has random-order competitive ratio better than $3-o(1)$, even with uniform costs on a prescribed candidate set and a known horizon.
--
--   Differences from the source:
--   - generalization: a demand-point multiset of size N in the metric of Lemma 6.2 → a multiset of N points of X; reason: a witness inside X is in particular a multiset in the metric
--   - encoding: E[ALG]/OPT ≥ r → E[ALG] ≥ r · OPT; reason: OPT > 0 on these instances, so the two are equivalent
--   - encoding: a randomized online algorithm (knowing the metric, costs, horizon and demand distribution, possibly opening several facilities per round) → a probability mass function over deterministic online algorithms, each a map from the revealed request prefix to the finite set of candidates opened in that round, independent of the demand randomness; reason: on a fixed finite instance with fixed horizon only finitely many deterministic behaviours exist, so every randomized algorithm is such a mixture; the public data are fixed before the algorithm is chosen
--   - encoding: real costs with d(x, ∅) = +∞ → costs in [0, ∞] (ENNReal), with d(x, ∅) = ⊤; reason: an algorithm that leaves the open set empty in some round pays +∞, exactly as in the source
--   - encoding: expectation over the uniformly random arrival order → finite average over all n! permutations of the labeled copies; reason: this is exactly the finite uniform law; no measurability assumption is needed
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf, Theorem 1.3(a) (printed p. 2, PDF p. 4) and Theorem 6.1 (printed p. 18, PDF p. 20); proof on printed p. 21 (PDF p. 23)

import Definitions.Def_RankCutFacility_Shifted_Supplement_Online

noncomputable section
open scoped ENNReal

namespace RankCutFacility.Shifted.Supplement

/-- Theorem 1.3(a) / Theorem 6.1 (PDF pp. 4, 20; printed pp. 2, 18): for every `N ≥ 2` and every
randomized online algorithm on the unit-cost prescribed-candidate instance of Lemma 6.2, some
demand multiset of size `N` (here even inside `X`) has
`E[ALG] ≥ (3N/(N+3)) · OPT` under uniformly random arrival order. -/
theorem general_lower_bound (N : ℕ) (hN : 2 ≤ N) (ρ : PMF (OnlineAlg (LBFac N) (LBPoint N))) :
    ∃ w : Fin N → Fin (lbM N),
      ENNReal.ofReal (3 * (N : ℝ) / ((N : ℝ) + 3) *
          offlineOpt (lbDist N) (lbSite N) (lbUnitFee N) (fun i => (Sum.inl (w i) : LBPoint N))) ≤
        randExpected (lbDist N) (lbSite N) (lbUnitFee N) ρ
          (fun i => (Sum.inl (w i) : LBPoint N)) := by sorry

end RankCutFacility.Shifted.Supplement
