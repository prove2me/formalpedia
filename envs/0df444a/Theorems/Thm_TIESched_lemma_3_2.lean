-- Prove2me | Theorems.Thm_TIESched_lemma_3_2
-- name    : TIESched.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:47:16.754723+00:00
-- url     : https://prove2.me/theorems/a3ff86fa-f1ca-435a-88ce-010a818a7140
-- title:
--   Lemma 3.2 — lower bound under bounded interaction, with $|S|/\mathrm{OPT}(p)\le mL^2$
-- statement:
--   Fix $0\le\Gamma<(m+1)/2$. There is a constant $L=L(m,\Gamma)\ge1$ such that every feasible fractional allocation family $x$ with interaction order at most $m-1$ admits a nonempty instance $(S,p)$, $p\ge0$, with
--   $$C\big(p,x^S(p)\big)>\Gamma\,\mathrm{OPT}(p)\qquad\text{and}\qquad \frac{|S|}{\mathrm{OPT}(p)}\le mL^2,$$
--   in particular $\mathrm{OPT}(p)>0$.
--
--   This is the hard-instance half of the proof of Theorem 1; the ratio bound lets the additive loss of Lemma 3.3 be absorbed.
--
--   Differences from the source:
--   - reading: |S|/OPT(p) ≤ mL² → 0 < OPT(p) and |S| ≤ mL²·OPT(p); reason: avoids the junk value x/0 = 0; the proof gives OPT(p) ≥ 1/L on every nonempty instance of the support (p.18), so this is the stronger reading
--   - encoding: a constant L ≥ 1 → a real number L ≥ 1 quantified before x; reason: the constant is independent of x, as stated
--   - encoding: rules x^S, π^S on ℝ^{m×S}_{≥0} with values in X(S) → total functions on ℝ^{m×S}, with feasibility a separate predicate on nonnegative reports; reason: a family on the orthant extends to such a total function, and the hypotheses read nonnegative reports only
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), Lemma 3.2, p.10 (restated p.18)

import Mathlib
import Definitions.Def_TIESched_interaction

set_option autoImplicit false

namespace TIESched

/-- **Lemma 3.2 (Lower bound under bounded interaction)** (Wang, Xu, Zhang, arXiv:2611.05142,
Lemma 3.2, p.10, restated p.18). Fix `0 ≤ Γ < (m + 1)/2`. Every feasible fractional allocation
family `x` with interaction order at most `m − 1` admits an instance `(S, p)` with
`C(p, x^S(p)) > Γ · OPT(p)`. Moreover, there is a constant `L = L(m, Γ) ≥ 1`, independent of `x`,
such that the instance can be chosen to satisfy `|S|/OPT(p) ≤ mL²`.

**Formalization Note.** `L` is quantified before `x`. The ratio bound is stated as `OPT(p) > 0` and
`|S| ≤ mL² · OPT(p)` (no division), and the instance is nonnegative and nonempty. -/
theorem lemma_3_2 (m : ℕ) [NeZero m] (hm : 2 ≤ m) (Γ : ℝ) (hΓ0 : 0 ≤ Γ)
    (hΓ : Γ < ((m : ℝ) + 1) / 2) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ x : AllocFamily m, Feasible x → HasInteractionOrderLE x (m - 1) →
      ∃ (S : Finset ℕ) (p : Fin m → S → ℝ), IsNonneg p ∧ S.Nonempty ∧ 0 < OPT p ∧
        Γ * OPT p < makespan p (x S p) ∧ (S.card : ℝ) ≤ (m : ℝ) * L ^ 2 * OPT p := by sorry

end TIESched
