-- Prove2me | Theorems.Thm_PersuasionByParts_Known_single_cutoff_experiment
-- name    : PersuasionByParts.Known.single_cutoff_experiment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:35.417735+00:00
-- url     : https://prove2.me/theorems/149624ca-340c-4136-a139-b8198867deb7
-- title:
--   Lemma 2.4 — Sparse product experiment and the single-pool event
-- statement:
--   Fix any product prior $P$ with $n\ge1$ integrable real coordinates, $q\in(0,1]$ and $t\le m_X(q)$. Form the targets $h_i$, capacities $b_i$ and $B=\sum_i b_i$ as in §2.1. Let $\Pi$ be the actual product experiment in which source $i$ pools its top-$s_i$ mass for
--
--   $$s_i=\frac q6\frac{b_i}{B}\quad\text{if }B\ge q/6,$$
--
--   and every source reveals if $B<q/6$. A zero individual pooling mass means full revelation. Let $N$ count pool tags and $Y_\Pi$ be this experiment's posterior sum. Both bounds concern this same experiment:
--
--   $$\mathbb E[N]\le q/6,\qquad \mathbb P(Y_\Pi\ge t,\ N\le1)\ge\frac{q^2}{36}.$$
--
--   The event retains the restriction to at most one pooling source. The theorem covers both capacity regimes and provides a concrete feasible experiment for the cutoff guarantee.
--
--   Differences from the source:
--   - encoding: n ≥ 1 coordinates indexed by [n], integrable real laws, and a measurable nondecreasing decision function into [0,1] → Fin n with 0 < n, a Prior of probability measures with Integrable id, and a Decision whose real values lie in Icc 0 1; reason: bijective relabeling and explicit standing assumptions from §1.1; every source prior and decision function is included
--   - encoding: suprema over all joint or independent coordinate experiments and their posterior mean payoffs → sSup of actual payoffs over Markov kernels with arbitrary small measurable signal spaces, with posterior disintegration and product signal laws; reason: the state spaces are standard Borel; disintegration gives conditional means almost surely, and independence makes the product posterior additive; no finite-signal or deterministic restriction and no maximizing experiment is assumed
--   - encoding: fractional-atom top-s pools and their quantile means for 0 < s ≤ 1 → the published upper quantile integral divided by s, the exact boundary-atom fraction, explicit zero/all selectors, and independent uniform randomization into Unit ⊕ ℝ pool/reveal tags; reason: interior quantiles are finite for arbitrary real probability laws; endpoint quantile values affect only a null set in the integral, and a zero-mass pool is never treated as a positive-mass conditional mean
--   - encoding: max of the feasible positive pooling masses, with empty maximum zero → capacity uses sSup of the bounded feasible set and returns zero on the empty set; IsGreatest is asserted in the joint-value theorem whenever the set is nonempty; reason: this encodes the same maximum without assuming attainment as a hypothesis; all feasible masses lie in (0,1]
--   - encoding: the integer number N of sources that pool → the real-valued finite sum of the indicators of pool tags; reason: the real embedding preserves the integer count, its expectation and the event N ≤ 1; reveal tags remain distinct even if numerical posterior means coincide
-- source:
--   Shuyuan Jia, Kangning Wang, Renzhe Xu, Persuasion by Parts, STOC 2027 submission #314 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/314.pdf, printed p. 8 / PDF p. 9, Lemma 2.4; construction and standing assumptions on printed pp. 7–8 / PDF pp. 8–9

import Mathlib
import Definitions.Def_PersuasionByParts_Known_Pooling

open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known

/-- Lemma 2.4, printed p. 8 / PDF p. 9: both claims refer to the same explicitly
constructed experiment, in both capacity regimes. -/
theorem single_cutoff_experiment {n : ℕ} (P : Prior n) (hn : 0 < n)
    (q t : ℝ) (hq : q ∈ Ioc 0 1) (ht : t ≤ poolMean (sumLaw P) q) :
    let E := sparseExperiment P q t
    (∫ s, poolCount s ∂productSignalLaw P E) ≤ q / 6 ∧
    (productSignalLaw P E).real
      {s | t ≤ productPosterior P E s ∧ poolCount s ≤ 1} ≥ q ^ 2 / 36 := by sorry

end PersuasionByParts.Known
