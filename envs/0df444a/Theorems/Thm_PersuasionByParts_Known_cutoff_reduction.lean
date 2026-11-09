-- Prove2me | Theorems.Thm_PersuasionByParts_Known_cutoff_reduction
-- name    : PersuasionByParts.Known.cutoff_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:19.709177+00:00
-- url     : https://prove2.me/theorems/ba69d2dd-9a76-412b-a2ed-de36671caecb
-- title:
--   Lemma 2.2 — Reduction from all cutoffs to all decision functions
-- statement:
--   Fix any product prior $P$ with $n\ge1$ integrable real coordinates and any real $c>0$. Suppose that for every real cutoff $t$,
--
--   $$V_{\rm prod}(t)\ge c\,V_{\rm joint}(t)^2.$$
--
--   Then every measurable nondecreasing decision function $g:\mathbb R\to[0,1]$ satisfies
--
--   $$V_{\rm prod}(g)\ge\frac c4 V_{\rm joint}(g)^2.$$
--
--   The all-cutoff comparison is the hypothesis of this reduction alone. It is not a condition on the goal's prior. Both values are actual suprema; no joint optimizer, continuity of $g$, or finite set of cutoffs is assumed. The result transfers a uniform cutoff bound to the complete decision-function class.
--
--   Differences from the source:
--   - encoding: n ≥ 1 coordinates indexed by [n], integrable real laws, and a measurable nondecreasing decision function into [0,1] → Fin n with 0 < n, a Prior of probability measures with Integrable id, and a Decision whose real values lie in Icc 0 1; reason: bijective relabeling and explicit standing assumptions from §1.1; every source prior and decision function is included
--   - encoding: suprema over all joint or independent coordinate experiments and their posterior mean payoffs → sSup of actual payoffs over Markov kernels with arbitrary small measurable signal spaces, with posterior disintegration and product signal laws; reason: the state spaces are standard Borel; disintegration gives conditional means almost surely, and independence makes the product posterior additive; no finite-signal or deterministic restriction and no maximizing experiment is assumed
-- source:
--   Shuyuan Jia, Kangning Wang, Renzhe Xu, Persuasion by Parts, STOC 2027 submission #314 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/314.pdf, printed p. 7 / PDF p. 8, Lemma 2.2

import Mathlib
import Definitions.Def_PersuasionByParts_Known_Model

open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known

/-- Lemma 2.2, printed p. 7 / PDF p. 8: compare every cutoff, then every measurable
nondecreasing decision function; no joint maximizer is required. -/
theorem cutoff_reduction {n : ℕ} (P : Prior n) (hn : 0 < n)
    (c : ℝ) (hc : 0 < c)
    (hcutoff : ∀ t : ℝ, productCutoff P t ≥ c * jointCutoff P t ^ 2) :
    ∀ g : Decision, productValue P g ≥ (c / 4) * jointValue P g ^ 2 := by sorry

end PersuasionByParts.Known
