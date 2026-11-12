-- Prove2me | Theorems.Thm_PersuasionByParts_Known_joint_cutoff_value
-- name    : PersuasionByParts.Known.joint_cutoff_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:33.901943+00:00
-- url     : https://prove2.me/theorems/516937f6-ecae-459f-b3f1-0e3456bffedd
-- title:
--   Lemma 1.3 — Joint cutoff value, maximum and top-pool attainment
-- statement:
--   Fix any product prior $P$ with $n\ge1$ integrable real coordinates, and any cutoff $t\in\mathbb R$. Let $\mu_X$ be the law of their sum $X$, and let $m_X$ denote its top-mass mean. Then
--
--   $$V_{\rm joint}(t)=\max\{s\in(0,1]:m_X(s)\ge t\},$$
--
--   with empty maximum zero. When the feasible set is nonempty, this value is its greatest element. The actual joint experiment that pools the top-$V_{\rm joint}(t)$ mass of $X$ and otherwise reveals $X$ achieves the value $V_{\rm joint}(t)$. If the value is zero, the kernel has no positive-mass pool. For every $q\in(0,1]$,
--
--   $$V_{\rm joint}(t)\ge q\quad\Longleftrightarrow\quad m_X(q)\ge t.$$
--
--   The characterization relates arbitrary joint experiments to the explicit top-pool construction. It supplies the exact joint benchmark used in the quadratic comparison.
--
--   Differences from the source:
--   - encoding: n ≥ 1 coordinates indexed by [n], integrable real laws, and a measurable nondecreasing decision function into [0,1] → Fin n with 0 < n, a Prior of probability measures with Integrable id, and a Decision whose real values lie in Icc 0 1; reason: bijective relabeling and explicit standing assumptions from §1.1; every source prior and decision function is included
--   - encoding: suprema over all joint or independent coordinate experiments and their posterior mean payoffs → sSup of actual payoffs over Markov kernels with arbitrary small measurable signal spaces, with posterior disintegration and product signal laws; reason: the state spaces are standard Borel; disintegration gives conditional means almost surely, and independence makes the product posterior additive; no finite-signal or deterministic restriction and no maximizing experiment is assumed
--   - encoding: fractional-atom top-s pools and their quantile means for 0 < s ≤ 1 → the published upper quantile integral divided by s, the exact boundary-atom fraction, explicit zero/all selectors, and independent uniform randomization into Unit ⊕ ℝ pool/reveal tags; reason: interior quantiles are finite for arbitrary real probability laws; endpoint quantile values affect only a null set in the integral, and a zero-mass pool is never treated as a positive-mass conditional mean
--   - encoding: max of the feasible positive pooling masses, with empty maximum zero → capacity uses sSup of the bounded feasible set and returns zero on the empty set; IsGreatest is asserted in the joint-value theorem whenever the set is nonempty; reason: this encodes the same maximum without assuming attainment as a hypothesis; all feasible masses lie in (0,1]
-- source:
--   Shuyuan Jia, Kangning Wang, Renzhe Xu, Persuasion by Parts, STOC 2027 submission #314 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/314.pdf, printed p. 3 / PDF p. 4, Lemma 1.3

import Mathlib
import Definitions.Def_PersuasionByParts_Known_Pooling

open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known

/-- Lemma 1.3, printed p. 3 / PDF p. 4: maximum, its actual top-pool attainment,
and both directions of the characterization, including an empty capacity set. -/
theorem joint_cutoff_value {n : ℕ} (P : Prior n) (hn : 0 < n) (t : ℝ) :
    jointCutoff P t = capacity (sumLaw P) t ∧
    ((capacitySet (sumLaw P) t).Nonempty →
      IsGreatest (capacitySet (sumLaw P) t) (jointCutoff P t)) ∧
    jointPayoff P (jointPool P (jointCutoff P t)) (cutoff t) = jointCutoff P t ∧
    (∀ q : ℝ, q ∈ Ioc 0 1 →
      (q ≤ jointCutoff P t ↔ t ≤ poolMean (sumLaw P) q)) := by sorry

end PersuasionByParts.Known
