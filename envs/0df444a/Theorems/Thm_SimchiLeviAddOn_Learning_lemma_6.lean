-- Prove2me | Theorems.Thm_SimchiLeviAddOn_Learning_lemma_6
-- name    : SimchiLeviAddOn.Learning.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:59:52.864288+00:00
-- url     : https://prove2.me/theorems/517b6c04-0098-4257-b542-bba374f61894
-- title:
--   Lemma 6 — good-event episode regret
-- statement:
--   Fix an operational instance, epsilon > 0, any completed UCB-Add-On controller and any completion of the zero-count event comparisons. There is a positive finite K₂ independent of T such that for every integer T >= 1 the expected regret of episodes starting in the complement of the literal event E is at most
--
--   $$K_2 NM\widehat p(\lambda^{-1}\sqrt{UT\log T}+\varepsilon\sqrt T).$$
--
--   The final episode is truncated at T. K₂ precedes every horizon. Lambda uses total primary demand, not core-only demand. A zero lambda gives infinity.
--
--   Differences from the source:
--   - encoding: positive product counts and finite nonempty nonnegative real price sets → positive natural dimensions and injectively labelled real menus with Fin indices; reason: every finite real menu admits this labelling; cardinalities, arbitrary real values and ties are preserved
--   - reading: the supportive index set is printed as {1,...,N} on page 7 and the supportive UCB empirical mean has subscript n on page 16 → supportive products use Fin M and their own primary empirical means; reason: the revenue formulas and page-15 parameter definitions index these quantities by the M supportive products
--   - reading: independent Bernoulli demands across products and identical periods → fresh conditional independent primary draws and independent add-on Bernoulli draws per core purchase; reason: this makes explicit the stationary bandit reading of Sections 2 and 4 with the same four mean tables
--   - generalization: zero-counter UCB values and zero-start doubling stops are unspecified → all causal [0,1] UCB completions and almost surely finite positive zero-start stopping completions, enforcing positive-count doubling; reason: this includes every completion consistent with the defined branches, including UCB=1 and first-observation stopping
--   - generalization: the bad-event comparison is undefined at count zero → every history-determined Boolean completion for each zero-count comparison; reason: all interpretations are included; the positive-count radius stays exactly 2 log(t)/count
--   - encoding: randomized nonanticipating decisions and expectations over observations → history-dependent action PMFs and post-observation stopping probabilities, multiplied finite kernels and finite expectation sums; reason: conditional kernels cover private randomness without unobserved demand in the history; finite sums cannot default to zero for nonintegrability
--   - reading: nested conditional expectations at random episode starts in (8)-(10) → expected indicator-weighted regret evaluated at the actual episode-start history, with final episode truncated at T; reason: condition first on the starting history and then average; event weighting is defined also at probability-zero events
--   - encoding: a regret bound using reciprocal lambda → an extended nonnegative bound, infinite at lambda=0, and ENNReal.ofReal of signed regret; reason: comparison is equivalent for finite nonnegative upper bounds and retains zero-arrival instances without real division-by-zero defaults
--   - reading: the discounted true mean in the page-17 event has a time subscript → the discounted true mean is the fixed beta-prime table at the discount price; reason: Sections 2 and 4 define fixed unknown means; only empirical estimates vary with time
--   - reading: an associated counter is doubled within an episode → stop after the first observation at which a positive-start associated count reaches or exceeds twice its starting value; reason: add-on counters can increase by up to N in one period, so a crossing can overshoot equality; primary counters and all specified positive-count stops remain enforced
-- source:
--   Simchi-Levi, Sun and Zhang, arXiv:2005.00947v1 (2 May 2020), https://arxiv.org/abs/2005.00947v1, Lemma 6, p. 19 (same PDF page)

import Definitions.Def_SimchiLeviAddOn_Learning_Online

open scoped ENNReal

namespace SimchiLeviAddOn.Learning

theorem lemma_6 (X : Market) (d : Tables X) (hd : IsDemand X d)
    (hX : Operational X) (ε : ℝ) (hε : 0 < ε) (A : Controller X)
    (hA : IsAlgorithm X d ε A) (e : EventCompletion X) :
    ∃ K₂ : ℝ, 0 < K₂ ∧ ∀ T : ℕ, 1 ≤ T →
      ENNReal.ofReal (eventRegret X d A e false T) ≤
        ENNReal.ofReal K₂ * regretScale X d ε T := by sorry

end SimchiLeviAddOn.Learning
