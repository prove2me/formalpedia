-- Prove2me | Theorems.Thm_UnconditionalKLS_Dunkl_lemma_3_4
-- name    : UnconditionalKLS.Dunkl.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T20:08:41.516357+00:00
-- url     : https://prove2.me/theorems/0381b05b-c033-45e6-8675-4ca69ae0e871
-- title:
--   Lemma 3.4 — weighted unconditional spectral estimate
-- statement:
--   Let $S>0$, let $W$ satisfy (2.4), and write $\eta$ and $\lambda$ for the auxiliary law and its gap. Let $g$ be unconditional, weakly differentiable on the open orthants, with $\mathbb E_\eta[c_i(g^2+|\nabla g|^2)]<\infty$ for the chosen coordinate $i$. Then
--   $$\left(\lambda-\frac3{2S^2}\right)\left(\mathbb E_\eta[c_ig^2]-\frac{\mathbb E_\eta[c_ig]^2}{\mathbb E_\eta[c_i]}\right)\le\mathbb E_\eta[c_i|\nabla g|^2].$$
--   No positivity assumption is placed on the prefactor. This is the weighted unconditional estimate, on the weighted finite-energy test domain used by the source's approximation extension. Its denominator is positive for the actual auxiliary law and $S>0$.
--
--   Differences from the source:
--   - encoding: functions on real Euclidean space with the paper’s analytic domains → Fin n coordinates, L² equivalence classes and canonical graph/form completions; extended nonnegative infima; reason: these represent the same objects; positive dimensions are retained and finite integrals are guarded
--   - encoding: unconditional test functions and the Appendix A.4 extension → unconditional weak tests with the weighted square-integrability condition; reason: the weighted Sobolev domain makes test-function integrability precise and includes the quotients of Appendix A.4
--   - generalization: unconditional legitimate test functions of Lemma 3.4 → all unconditional weak tests with finite weighted square norm and gradient energy; reason: weighted Sobolev approximation extends the estimate; smooth source tests and the Appendix A.4 quotients are included
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), p. 19, Lemma 3.4; contextual domains in Appendix A, pp. 31–38. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Domains

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl
theorem lemma_3_4 {n : ℕ} (hn : 0 < n) (S : ℝ) (W : Fn n)
    (hS : 0 < S) (hW : Admissible W) (g : Fn n) (i : Fin n)
    (hg : WeightedTest S W g i) (heven : Even (eta S W) g) :
    weightedEstimate S W g i := by sorry
end UnconditionalKLS.Dunkl
