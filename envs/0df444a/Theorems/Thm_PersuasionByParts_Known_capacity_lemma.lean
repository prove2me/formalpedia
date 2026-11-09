-- Prove2me | Theorems.Thm_PersuasionByParts_Known_capacity_lemma
-- name    : PersuasionByParts.Known.capacity_lemma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:36.64065+00:00
-- url     : https://prove2.me/theorems/16be52ff-6837-448f-8be6-9457a9c4fcd6
-- title:
--   Lemma 2.3 — Capacity inequality and strict revelation consequence
-- statement:
--   Fix any product prior $P$ with $n\ge1$ integrable real coordinates. Let $q\in(0,1]$ and $t\le m_X(q)$. For the derived quantities
--
--   $$h_i=t-F_{X_{-i}}^{-1}(1-q/3),\quad b_i=\max\{s\in(0,1]:m_{P_i}(s)\ge h_i\},\quad B=\sum_i b_i,\quad p=P(X\ge t),$$
--
--   where empty capacities are zero, the full capacity comparison is
--
--   $$B+\frac{18p}{q}\ge\frac{2q}{3}.$$
--
--   In particular,
--
--   $$B<q/6\quad\Longrightarrow\quad p>\frac{q^2}{36}.$$
--
--   This relates the total locally available pooling mass to full revelation. The zero-capacity case is included, and no positive-capacity assumption is imposed.
--
--   Differences from the source:
--   - encoding: n ≥ 1 coordinates indexed by [n], integrable real laws, and a measurable nondecreasing decision function into [0,1] → Fin n with 0 < n, a Prior of probability measures with Integrable id, and a Decision whose real values lie in Icc 0 1; reason: bijective relabeling and explicit standing assumptions from §1.1; every source prior and decision function is included
--   - encoding: fractional-atom top-s pools and their quantile means for 0 < s ≤ 1 → the published upper quantile integral divided by s, the exact boundary-atom fraction, explicit zero/all selectors, and independent uniform randomization into Unit ⊕ ℝ pool/reveal tags; reason: interior quantiles are finite for arbitrary real probability laws; endpoint quantile values affect only a null set in the integral, and a zero-mass pool is never treated as a positive-mass conditional mean
--   - encoding: max of the feasible positive pooling masses, with empty maximum zero → capacity uses sSup of the bounded feasible set and returns zero on the empty set; IsGreatest is asserted in the joint-value theorem whenever the set is nonempty; reason: this encodes the same maximum without assuming attainment as a hypothesis; all feasible masses lie in (0,1]
-- source:
--   Shuyuan Jia, Kangning Wang, Renzhe Xu, Persuasion by Parts, STOC 2027 submission #314 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/314.pdf, printed p. 8 / PDF p. 9, Lemma 2.3; standing q,t assumptions and capacity definitions on printed p. 7 / PDF p. 8

import Mathlib
import Definitions.Def_PersuasionByParts_Known_Pooling

open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known

/-- Lemma 2.3, printed p. 8 / PDF p. 9, with the standing hypotheses on p. 7. -/
theorem capacity_lemma {n : ℕ} (P : Prior n) (hn : 0 < n)
    (q t : ℝ) (hq : q ∈ Ioc 0 1) (ht : t ≤ poolMean (sumLaw P) q) :
    totalCapacity P q t + 18 * revelationProbability P t / q ≥ 2 * q / 3 ∧
    (totalCapacity P q t < q / 6 → revelationProbability P t > q ^ 2 / 36) := by sorry

end PersuasionByParts.Known
