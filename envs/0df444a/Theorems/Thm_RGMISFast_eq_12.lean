-- Prove2me | Theorems.Thm_RGMISFast_eq_12
-- name    : RGMISFast.eq_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:21.3502+00:00
-- url     : https://prove2.me/theorems/e3c15aca-b041-4ddc-a547-6733ad1e96c9
-- title:
--   Eq. (12): $\Pr[\neg E_h]\le(320+1+\tfrac14)e^{-(h+8)}<e^{-h}$
-- statement:
--   Let $G$ be a finite simple graph with all degrees at most $\Delta\ge2$ and root $u^*$, with i.i.d. Exp(1) ranks, and let $h\ge0$. The good event $E_h$ (conclusions of Lemmas 3.1, 3.2 and A.1 at $L=h+8$) satisfies
--   $$
--   \Pr[\neg E_h]\le\Big(320+1+\frac14\Big)e^{-(h+8)}<e^{-h}. \tag{12}
--   $$
--
--   Together with Proposition 4.2, this is the tail bound of Theorem 1.1.
--
--   **Formalization Note** Both inequalities are stated; the probability is the measure of the complement of $E_h$ under the product Exp(1) law.
--
--   Differences from the source:
--   - encoding: Pr[¬E_h] → the (outer) measure of the set where `GoodEvent G Δ u (h + 8)` fails; reason: equivalent for a probability measure
--   - generalization: h an integer ≥ 1 (§3 opening, p.13: "We parameterize the bad events by an integer h ≥ 1"), then h = L − 8 with L ≥ 8 → every real h ≥ 0; reason: the paper also uses real h ≥ 0 (§4, Theorem 1.1); (12) is the union bound of Lemmas 3.1, 3.2 and A.1 at L = h + 8 ≥ 8, which hold for every real L ≥ 8; integer h ≥ 1 is a special case
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), eq. (12), p.14 (PDF p.16)

import Mathlib
import Definitions.Def_RGMISFast_GoodEvent
import Definitions.Def_RGMISFast_rankLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RGMISFast

/-- Eq. (12) (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…), §3, p.14): the union bound gives
`Pr[¬E_h] ≤ (320 + 1 + 1/4) e^{−(h+8)} < e^{−h}`.

**Formalization Note** `E_h = GoodEvent G Δ u (h + 8)`, for every real `h ≥ 0`; both
inequalities are stated. The probability is the (outer) measure of the complement of `E_h` under
the i.i.d. Exp(1) rank law. All degrees are at most `∆`, `∆ ≥ 2`. -/
theorem eq_12 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (u : V) (h : ℝ) (hh : 0 ≤ h) :
    rankLaw V {r | ¬ GoodEvent G Δ u (h + 8) r} ≤
        ENNReal.ofReal ((320 + 1 + 1 / 4) * Real.exp (-(h + 8))) ∧
      (320 + 1 + 1 / 4) * Real.exp (-(h + 8)) < Real.exp (-h) := by sorry

end RGMISFast
