-- Prove2me | Theorems.Thm_SimchiLeviAddOn_Learning_theorem_2
-- name    : SimchiLeviAddOn.Learning.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:59:59.138881+00:00
-- url     : https://prove2.me/theorems/ebc586a5-ae73-4240-9979-83115499a5dd
-- title:
--   Theorem 2 — UCB-Add-On regret bound
-- statement:
--   There is a positive absolute C such that for every operational instance with arbitrary demand tables in [0,1] and every epsilon > 0, there is an integer T₀ >= 2 such that every completed UCB-Add-On controller and every integer T >= T₀ satisfy
--
--   $$\operatorname{Regret}(T) \le C NM\widehat p(\lambda^{-1}\sqrt{UT\log T}+\varepsilon\sqrt T).$$
--
--   Regret is the expectation of cumulative clairvoyant benchmark minus revenue of the actual policies. Algorithms 1 and 2 are represented in full, with parameter-level UCBs, K=ceil(sqrt(t)/epsilon), opportunity counters, doubling episodes, all ties and all causal zero-count completions. The constant precedes instance parameters and epsilon; T₀ precedes all controllers. The price scale uses core and original prices, U is the largest of the three menu cardinalities, and lambda minimizes the probability of nonzero total primary demand. At lambda=0 the bound is infinity.
--
--   Differences from the source:
--   - encoding: positive product counts and finite nonempty nonnegative real price sets → positive natural dimensions and injectively labelled real menus with Fin indices; reason: every finite real menu admits this labelling; cardinalities, arbitrary real values and ties are preserved
--   - reading: the supportive index set is printed as {1,...,N} on page 7 and the supportive UCB empirical mean has subscript n on page 16 → supportive products use Fin M and their own primary empirical means; reason: the revenue formulas and page-15 parameter definitions index these quantities by the M supportive products
--   - reading: independent Bernoulli demands across products and identical periods → fresh conditional independent primary draws and independent add-on Bernoulli draws per core purchase; reason: this makes explicit the stationary bandit reading of Sections 2 and 4 with the same four mean tables
--   - generalization: zero-counter UCB values and zero-start doubling stops are unspecified → all causal [0,1] UCB completions and almost surely finite positive zero-start stopping completions, enforcing positive-count doubling; reason: this includes every completion consistent with the defined branches, including UCB=1 and first-observation stopping
--   - encoding: randomized nonanticipating decisions and expectations over observations → history-dependent action PMFs and post-observation stopping probabilities, multiplied finite kernels and finite expectation sums; reason: conditional kernels cover private randomness without unobserved demand in the history; finite sums cannot default to zero for nonintegrability
--   - encoding: a regret bound using reciprocal lambda → an extended nonnegative bound, infinite at lambda=0, and ENNReal.ofReal of signed regret; reason: comparison is equivalent for finite nonnegative upper bounds and retains zero-arrival instances without real division-by-zero defaults
--   - reading: the displayed Big-O rate → one positive absolute multiplier before instances and epsilon, with an eventual threshold before all controllers; reason: the dimension, price and menu scaling is retained uniformly; the threshold may depend on the instance and epsilon but not tie choices or realized runs
--   - reading: an associated counter is doubled within an episode → stop after the first observation at which a positive-start associated count reaches or exceeds twice its starting value; reason: add-on counters can increase by up to N in one period, so a crossing can overshoot equality; primary counters and all specified positive-count stops remain enforced
-- source:
--   Simchi-Levi, Sun and Zhang, arXiv:2005.00947v1 (2 May 2020), https://arxiv.org/abs/2005.00947v1, Theorem 2, p. 16 (same PDF page)

import Definitions.Def_SimchiLeviAddOn_Learning_Online

namespace SimchiLeviAddOn.Learning

theorem theorem_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Market) (d : Tables X), IsDemand X d → Operational X →
      ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℕ, 2 ≤ T₀ ∧
        ∀ A : Controller X, IsAlgorithm X d ε A → ∀ T : ℕ, T₀ ≤ T →
          ENNReal.ofReal (regret X d A T) ≤
            ENNReal.ofReal C * regretScale X d ε T := by sorry

end SimchiLeviAddOn.Learning
