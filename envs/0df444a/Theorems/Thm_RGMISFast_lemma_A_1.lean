-- Prove2me | Theorems.Thm_RGMISFast_lemma_A_1
-- name    : RGMISFast.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:19.884319+00:00
-- url     : https://prove2.me/theorems/d750ffc5-ac8d-4e31-b433-755340cc6911
-- title:
--   Lemma A.1: low ranks, $|\Gamma_{<a_M}(A)|\le2(|A|\log(8e\Delta)+L+2)$ w.p. $\ge1-e^{-L}/4$
-- statement:
--   Let $G$ be a finite simple graph with all degrees at most $\Delta\ge2$ and root $u^*$, with i.i.d. Exp(1) ranks, and let $L\ge8$. With probability at least $1-e^{-L}/4$, every root-connected set $A$ satisfies
--   $$
--   |\Gamma_{<a_M}(A)|\le 2\big(|A|\log(8e\Delta)+L+2\big). \tag{32}
--   $$
--
--   This controls the part of an admissible tree below the last time interval.
--
--   **Formalization Note** The statement bounds the measure of the failure event under the product Exp(1) law by $e^{-L}/4$; $\log$ is the natural logarithm. $L\ge8$ is the range $L=h+8$, $h\ge0$, fixed at the start of App. A.
--
--   Differences from the source:
--   - encoding: with probability at least 1 − e^{−L}/4 → the (outer) measure of the failure set is at most e^{−L}/4; reason: equivalent for a probability measure
--   - generalization: L = h + 8 "as in Section 3", where §3 takes h an integer ≥ 1 → every real L ≥ 8; reason: §4 and Theorem 1.1 use real h ≥ 0, i.e. real L ≥ 8; the proof (k_j = ⌈(j log(8e∆) + L + 2)/log 2⌉) works for every real L ≥ 8; integer h ≥ 1 is a special case
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), Lemma A.1, eq. (32), p.29 (PDF p.31)

import Mathlib
import Definitions.Def_RGMISFast_GoodEvent
import Definitions.Def_RGMISFast_rankLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RGMISFast

/-- Lemma A.1 (Low Ranks; Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…), p.29): with probability at least `1 − e^{−L}/4`, every
root-connected set `A` satisfies `|Γ_{<a_M}(A)| ≤ 2(|A| log(8e∆) + L + 2)` (32).

**Formalization Note** `L = h + 8` with `h ≥ 0` ("Fix L = h + 8 as in Section 3", p.29), stated
for every real `L ≥ 8`. The bad event `¬ LowRankEvent` has (outer) measure at most `e^{−L}/4`
under the i.i.d. Exp(1) rank law. `log` is the natural logarithm; `M = Mof Δ`; all degrees are at
most `∆`, `∆ ≥ 2`. -/
theorem lemma_A_1 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (u : V) (L : ℝ)
    (hL : 8 ≤ L) :
    rankLaw V {r | ¬ LowRankEvent G Δ u L r} ≤ ENNReal.ofReal (Real.exp (-L) / 4) := by sorry

end RGMISFast
