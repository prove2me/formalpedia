-- Prove2me | Theorems.Thm_PersuasionByParts_Known_quadratic_guarantee
-- name    : PersuasionByParts.Known.quadratic_guarantee
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:49.852637+00:00
-- url     : https://prove2.me/theorems/aba2e512-f82c-4296-9099-8f2f6706fdac
-- title:
--   Theorem 2.1 — Quadratic guarantees for known decision functions
-- statement:
--   Let $n\ge1$, let $P=\bigotimes_{i=1}^n P_i$ be any product prior with $\int|x|\,dP_i(x)<\infty$, let $t\in\mathbb R$, and let $g:\mathbb R\to[0,1]$ be any measurable nondecreasing decision function. Joint experiments can condition on the entire vector; product experiments use coordinate kernels with independent private randomness. Their optimal values are the suprema of their actual expected decision payoffs. Then both comparisons hold:
--
--   $$V_{\rm prod}(t)\ge\frac1{36}V_{\rm joint}(t)^2,\qquad V_{\rm prod}(g)\ge\frac1{144}V_{\rm joint}(g)^2.$$
--
--   The constants are uniform in the number of sources, their integrable real laws, the cutoff and the decision function. No sign, bounded-support, atomlessness, identical-law or continuity restriction is imposed. The designer may tailor the experiment to the known decision function. This is the full two-clause result and the sole mission goal.
--
--   Differences from the source:
--   - encoding: n ≥ 1 coordinates indexed by [n], integrable real laws, and a measurable nondecreasing decision function into [0,1] → Fin n with 0 < n, a Prior of probability measures with Integrable id, and a Decision whose real values lie in Icc 0 1; reason: bijective relabeling and explicit standing assumptions from §1.1; every source prior and decision function is included
--   - encoding: suprema over all joint or independent coordinate experiments and their posterior mean payoffs → sSup of actual payoffs over Markov kernels with arbitrary small measurable signal spaces, with posterior disintegration and product signal laws; reason: the state spaces are standard Borel; disintegration gives conditional means almost surely, and independence makes the product posterior additive; no finite-signal or deterministic restriction and no maximizing experiment is assumed
-- source:
--   Shuyuan Jia, Kangning Wang, Renzhe Xu, Persuasion by Parts, STOC 2027 submission #314 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/314.pdf, printed p. 7 / PDF p. 8, Theorem 2.1; standing model assumptions on printed pp. 1–2 / PDF pp. 2–3

import Mathlib
import Definitions.Def_PersuasionByParts_Known_Model

open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known

/-- Theorem 2.1, printed p. 7 / PDF p. 8, both clauses and their exact constants. -/
theorem quadratic_guarantee {n : ℕ} (P : Prior n) (hn : 0 < n) (t : ℝ) (g : Decision) :
    productCutoff P t ≥ (1 / 36 : ℝ) * jointCutoff P t ^ 2 ∧
    productValue P g ≥ (1 / 144 : ℝ) * jointValue P g ^ 2 := by sorry

end PersuasionByParts.Known
