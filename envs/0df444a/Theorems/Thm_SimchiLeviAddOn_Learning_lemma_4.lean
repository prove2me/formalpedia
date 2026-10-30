-- Prove2me | Theorems.Thm_SimchiLeviAddOn_Learning_lemma_4
-- name    : SimchiLeviAddOn.Learning.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T02:00:02.84317+00:00
-- url     : https://prove2.me/theorems/308807c7-2dcc-4696-8ef5-44667275feca
-- title:
--   Lemma 4 — expected episode length
-- statement:
--   For every operational instance with arbitrary demand tables in [0,1], epsilon > 0, and any completed UCB-Add-On controller, condition on any positive-probability starting history of an episode. If the next period is t, the expected full episode length is at most t. Every causal completion of the undefined zero-count branches is included. The extended tail-sum expectation retains a possible infinite mean.
--
--   Differences from the source:
--   - encoding: positive product counts and finite nonempty nonnegative real price sets → positive natural dimensions and injectively labelled real menus with Fin indices; reason: every finite real menu admits this labelling; cardinalities, arbitrary real values and ties are preserved
--   - reading: the supportive index set is printed as {1,...,N} on page 7 and the supportive UCB empirical mean has subscript n on page 16 → supportive products use Fin M and their own primary empirical means; reason: the revenue formulas and page-15 parameter definitions index these quantities by the M supportive products
--   - reading: independent Bernoulli demands across products and identical periods → fresh conditional independent primary draws and independent add-on Bernoulli draws per core purchase; reason: this makes explicit the stationary bandit reading of Sections 2 and 4 with the same four mean tables
--   - generalization: zero-counter UCB values and zero-start doubling stops are unspecified → all causal [0,1] UCB completions and almost surely finite positive zero-start stopping completions, enforcing positive-count doubling; reason: this includes every completion consistent with the defined branches, including UCB=1 and first-observation stopping
--   - encoding: randomized nonanticipating decisions and expectations over observations → history-dependent action PMFs and post-observation stopping probabilities, multiplied finite kernels and finite expectation sums; reason: conditional kernels cover private randomness without unobserved demand in the history; finite sums cannot default to zero for nonintegrability
--   - reading: expected length of an episode starting at t → conditional expected full length after each positive-probability starting history, with t its length plus one; reason: the random start time is made precise by conditioning on its observed starting history
--   - reading: an associated counter is doubled within an episode → stop after the first observation at which a positive-start associated count reaches or exceeds twice its starting value; reason: add-on counters can increase by up to N in one period, so a crossing can overshoot equality; primary counters and all specified positive-count stops remain enforced
-- source:
--   Simchi-Levi, Sun and Zhang, arXiv:2005.00947v1 (2 May 2020), https://arxiv.org/abs/2005.00947v1, Lemma 4, p. 18 (same PDF page)

import Definitions.Def_SimchiLeviAddOn_Learning_Online

open scoped ENNReal

namespace SimchiLeviAddOn.Learning

theorem lemma_4 (X : Market) (d : Tables X) (hd : IsDemand X d)
    (hX : Operational X) (ε : ℝ) (hε : 0 < ε) (A : Controller X)
    (hA : IsAlgorithm X d ε A) (h : History X)
    (hh : 0 < extensionMass X d A [] h) (hstart : lastStop h = h.length) :
    expectedLength X d A h ≤ (h.length + 1 : ℝ≥0∞) := by sorry

end SimchiLeviAddOn.Learning
