-- Prove2me | Theorems.Thm_PriceRobustness_Main_proposition_2
-- name    : PriceRobustness.Main.proposition_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:39:21.301445+00:00
-- url     : https://prove2.me/theorems/6cd8302b-c4b6-4ba4-90be-ef23f774e79e
-- title:
--   Proposition 2(a)–(b): violation reduction and coefficient bound
-- statement:
--   Let $x^*$ be any optimal decision of the robust LP (7). Fix a row $i$, any maximizing protection pair $(S_i^*,t_i^*)$, and any minimizing weight index $r^*\in S_i^*\cup\{t_i^*\}$. Use the source coefficients $\gamma_{ij}=1$ on $S_i^*$ and $\hat a_{ij}|x_j^*|/(\hat a_{ir^*}|x_{r^*}^*|)$ off it, with the stated full-budget and zero-quotient conventions. Under Model U, with independent symmetric row noise in $[-1,1]$, the source asserts both
--   $$P\left\{\sum_j\tilde a_{ij}x_j^*>b_i\right\}\le P\left\{\sum_{j\in J_i}\gamma_{ij}\eta_{ij}\ge\Gamma_i\right\},$$
--   $$\gamma_{ij}\le1\quad(j\in J_i\setminus S_i^*).$$
--   The budget is any real number in $[0,|J_i|]$. The first event is strict and the second is non-strict. This is the sole numbered milestone used by the appendix's proof of Theorem 3. The coefficient assertion is retained as printed; the integer-budget counterexample is recorded separately in INSIGHTS.yaml, not removed by an added assumption.
--
--   Differences from the source:
--   - encoding: finite matrix indices and probability notation → Fin indices, an arbitrary measurable probability space, measurable real random variables and real-valued event probabilities; reason: finite relabeling and the standard measurable-probability convention preserve the source instances
--   - reading: the unbound j in the fractional term of Eq. (5) → the designated extra coordinate t; reason: the preceding model, the one-fractional-coordinate explanation and Eq. (9) fix that coordinate
--   - encoding: integer-budget endpoints on p. 6 and the pair notation of Proposition 2 → optional t and r, with S=J and no indices at full budget, including the empty row; reason: the outside branch is unused at full budget and no impossible extra index is required
--   - encoding: the quotient w_j/w_r with no convention when w_r=0 → real division assigns zero to a zero-denominator quotient; reason: this total-function extension retains otherwise undefined inputs and agrees with every defined quotient; no positivity hypothesis is added
--   - encoding: Model U defines eta=(a_tilde-a)/a_hat → realized entries are a+radius*eta on J, including zero radii; reason: the inverse representation agrees at positive radii and retains deterministic zero-radius entries without dividing by zero
-- source:
--   Bertsimas and Sim, The Price of Robustness, authors' preprint, August 2001; revised August, 2002; PDF SHA-256 63f0bffaff9128b706a084acc869e1020ce79adf86108ac23b5b0dd598f189cb; Proposition 2(a)–(b), p. 8; standing model §§2–3 and §5, p. 17

import Definitions.Def_PriceRobustness_Main_RobustModel
import Definitions.Def_PriceRobustness_Main_Protection
import Definitions.Def_PriceRobustness_Main_Noise

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace PriceRobustness.Main

theorem proposition_2 {m N : ℕ} (D : RobustModel m N) (x : Fin N → ℝ)
    (hx : D.Optimal x) (i : Fin m) (S : Finset (Fin N)) (t r : Option (Fin N))
    (hmax : MaximizesProtection (D.J i) (D.weight x i) (D.budget i) S t)
    (hmin : MinimizesSelected (D.weight x i) S t r)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (η : Fin N → Ω → ℝ) (hη : SymmetricNoise P (D.J i) η) :
    (P.real {ω | (∑ j, D.uncertainEntry η i j ω * x j) > D.nominal.b i} ≤
      P.real {ω | (∑ j ∈ D.J i, sourceGamma (D.weight x i) S r j * η j ω) ≥
        D.budget i}) ∧
    (∀ j ∈ D.J i, j ∉ S → sourceGamma (D.weight x i) S r j ≤ 1) := by sorry

end PriceRobustness.Main
