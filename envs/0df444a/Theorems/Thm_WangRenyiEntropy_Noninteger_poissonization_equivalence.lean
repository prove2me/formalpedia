-- Prove2me | Theorems.Thm_WangRenyiEntropy_Noninteger_poissonization_equivalence
-- name    : WangRenyiEntropy.Noninteger.poissonization_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:06.786228+00:00
-- url     : https://prove2.me/theorems/bb9f81e3-2c7d-4a84-989a-c5b89b5b4fbb
-- title:
--   Fact 1.2 — Poissonized and multinomial complexity equivalence
-- statement:
--   Fix any order $\alpha>0$, including the Shannon order $\alpha=1$. Let $S^\mathrm{Mul}_\alpha(d,\varepsilon)$ and $S^\mathrm{Poi}_\alpha(d,\varepsilon)$ be the least attainable budgets for a single randomized estimator of $H_\alpha(p)$ to have additive error at most $\varepsilon$ with probability at least $2/3$, uniformly over all $d$-letter probability laws. There are constants $c,C>0$, independent of $d\ge1$ and $\varepsilon>0$, such that
--   $$cS^\mathrm{Poi}_\alpha(d,\varepsilon)\le S^\mathrm{Mul}_\alpha(d,\varepsilon)\le CS^\mathrm{Poi}_\alpha(d,\varepsilon).$$
--   This comparison transfers sample-complexity statements between ordered iid samples and random-length Poisson samples, whose budget is their expected length.
--
--   Differences from the source:
--   - encoding: finite alphabet and nonnegative normalized real probability coordinates → Fin d with d ≥ 1 and the published IsLaw predicate, allowing zero coordinates; reason: relabeling preserves every finite nonempty alphabet and every probability law
--   - encoding: all estimators with success probability at least 2/3 → all maps from the discrete observed word to Borel probability measures on the real output, with their randomness integrated into success; reason: these maps are precisely randomized kernels on a countable discrete observation space; no dependence on the unknown law is permitted
--   - encoding: least sample budgets → extended nonnegative infima, with infinity for an empty feasible set; reason: avoids assigning zero when no estimator exists; preserves the Shannon branch of the source convention
-- source:
--   Qisheng Wang, STOC 2027 submission #447 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/447.pdf, printed 3 / PDF 5, Fact 1.2

import Mathlib
import Definitions.Def_WangRenyiEntropy_Noninteger_SamplingExperiment

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace WangRenyiEntropy.Noninteger

/-- Fact 1.2, printed p.3 / PDF p.5. All positive orders, including α=1.
Sample complexities are extended infima over unrestricted randomized estimators. -/
theorem poissonization_equivalence (α : ℝ) (hα : 0 < α) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ d : ℕ, 1 ≤ d → ∀ ε : ℝ, 0 < ε →
      ENNReal.ofReal c * poissonComplexity α ε d ≤ multinomialComplexity α ε d ∧
      multinomialComplexity α ε d ≤ ENNReal.ofReal C * poissonComplexity α ε d := by sorry

end WangRenyiEntropy.Noninteger
