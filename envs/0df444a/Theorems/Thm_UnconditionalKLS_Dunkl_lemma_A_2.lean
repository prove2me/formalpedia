-- Prove2me | Theorems.Thm_UnconditionalKLS_Dunkl_lemma_A_2
-- name    : UnconditionalKLS.Dunkl.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T20:08:48.331299+00:00
-- url     : https://prove2.me/theorems/c16d2590-d5e6-4c4f-96a5-06c7a0d0c4de
-- title:
--   Lemma A.2 — Lipschitz and polynomial-growth domains
-- statement:
--   Fix $S>0$ and $W$ satisfying (2.4). Let $f$ be locally Lipschitz on $\mathbb R^n$ and suppose $\mathbb E_\eta[f^2+|\nabla f|^2]<\infty$. Then
--   $$f\in D(A^{1/2}),\qquad\mathcal E(f)\le9\mathbb E_\eta|\nabla f|^2.$$
--   If additionally $f\in C^2$ and $f,\nabla f,\nabla^2 f$ have polynomial growth, then $f\in D(A)$, the expression (3.3) is in $L^2(\eta)$, and $Af$ equals that expression. Polynomial growth means a bound by $C(1+|x|)^m$ for one finite $C\ge0$ and natural $m$; using one bound for the sum of all three norms is equivalent to bounding them separately.
--
--   This includes noncompact functions, such as coordinate tests. Classical gradients of locally Lipschitz functions are used almost everywhere under the absolutely continuous auxiliary law; no smoothness is assumed for the first assertion.
--
--   Differences from the source:
--   - encoding: functions on real Euclidean space with the paper’s analytic domains → Fin n coordinates, L² equivalence classes and canonical graph/form completions; extended nonnegative infima; reason: these represent the same objects; positive dimensions are retained and finite integrals are guarded
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), p. 35, Lemma A.2; contextual domains in Appendix A, pp. 31–38. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Domains

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl
theorem lemma_A_2 {n : ℕ} (hn : 0 < n) (S : ℝ) (W f : Fn n)
    (hS : 0 < S) (hW : Admissible W) (hf : LocallyLipschitz f)
    (hfinite : Integrable (fun x => (f x)^2 + ‖grad f x‖^2) (eta S W)) :
    FormDomain S W f ∧
    energy S W f ≤ 9 * (∫ x, ‖grad f x‖^2 ∂eta S W) ∧
    (ContDiff ℝ 2 f → polynomialGrowth f →
      OperatorDomain S W f ∧ MemLp (expression S W f) 2 (eta S W) ∧
      action S W f = l2 (eta S W) (expression S W f)) := by sorry
end UnconditionalKLS.Dunkl
