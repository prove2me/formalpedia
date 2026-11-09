-- Prove2me | Theorems.Thm_PersuasionByParts_Known_experiment_wellposed
-- name    : PersuasionByParts.Known.experiment_wellposed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:35.513532+00:00
-- url     : https://prove2.me/theorems/589afd7f-cc32-4b0c-80dc-2bcb7c5dfb92
-- title:
--   §1.1 — Integrable posterior payoffs and bounded persuasion values
-- statement:
--   Let $P$ be any $n$-coordinate product prior, $n\ge1$, with integrable real marginals. Let $g:\mathbb R\to[0,1]$ be a measurable nondecreasing decision function. The sets of payoffs achievable by joint and product experiments are nonempty and bounded above, and
--
--   $$0\le V_{\rm prod}(g)\le1,\qquad 0\le V_{\rm joint}(g)\le1.$$
--
--   For every actual joint or product experiment, its posterior mean and its decision payoff are integrable, and its expected decision payoff belongs to $[0,1]$. For every real cutoff $t$, the corresponding achievable-payoff sets are also nonempty and bounded above, and both cutoff values belong to $[0,1]$.
--
--   This auxiliary statement makes the analytic well-posedness implicit in Definition 1.1 explicit. Its conclusions establish that the real suprema and expectations have their usual mathematical meanings, rather than default values on inadmissible inputs. It is supporting infrastructure, not another numbered milestone.
--
--   Differences from the source:
--   - encoding: n ≥ 1 coordinates indexed by [n], integrable real laws, and a measurable nondecreasing decision function into [0,1] → Fin n with 0 < n, a Prior of probability measures with Integrable id, and a Decision whose real values lie in Icc 0 1; reason: bijective relabeling and explicit standing assumptions from §1.1; every source prior and decision function is included
--   - encoding: suprema over all joint or independent coordinate experiments and their posterior mean payoffs → sSup of actual payoffs over Markov kernels with arbitrary small measurable signal spaces, with posterior disintegration and product signal laws; reason: the state spaces are standard Borel; disintegration gives conditional means almost surely, and independence makes the product posterior additive; no finite-signal or deterministic restriction and no maximizing experiment is assumed
-- source:
--   Shuyuan Jia, Kangning Wang, Renzhe Xu, Persuasion by Parts, STOC 2027 submission #314 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/314.pdf, printed pp. 1–2 / PDF pp. 2–3, §1.1 and Definition 1.1

import Mathlib
import Definitions.Def_PersuasionByParts_Known_Model

open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known

/-- Section 1.1, Definition 1.1: actual admissible payoffs are nonempty and bounded;
conditional means and bounded decision payoffs are integrable. No optimizer is assumed. -/
theorem experiment_wellposed {n : ℕ} (P : Prior n) (hn : 0 < n) (g : Decision) :
    (jointPayoffs P g).Nonempty ∧ BddAbove (jointPayoffs P g) ∧
    (productPayoffs P g).Nonempty ∧ BddAbove (productPayoffs P g) ∧
    jointValue P g ∈ Icc 0 1 ∧ productValue P g ∈ Icc 0 1 ∧
    (∀ E : JointExperiment n,
      Integrable (jointPosterior P E) (jointSignalLaw P E) ∧
      Integrable (fun s => g (jointPosterior P E s)) (jointSignalLaw P E) ∧
      jointPayoff P E g ∈ Icc 0 1) ∧
    (∀ E : ProductExperiment n,
      Integrable (productPosterior P E) (productSignalLaw P E) ∧
      Integrable (fun s => g (productPosterior P E s)) (productSignalLaw P E) ∧
      productPayoff P E g ∈ Icc 0 1) ∧
    (∀ t : ℝ,
      (jointPayoffs P (cutoff t)).Nonempty ∧ BddAbove (jointPayoffs P (cutoff t)) ∧
      (productPayoffs P (cutoff t)).Nonempty ∧ BddAbove (productPayoffs P (cutoff t)) ∧
      jointCutoff P t ∈ Icc 0 1 ∧ productCutoff P t ∈ Icc 0 1) := by sorry

end PersuasionByParts.Known
