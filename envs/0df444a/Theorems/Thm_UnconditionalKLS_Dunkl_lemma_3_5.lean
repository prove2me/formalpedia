-- Prove2me | Theorems.Thm_UnconditionalKLS_Dunkl_lemma_3_5
-- name    : UnconditionalKLS.Dunkl.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T20:08:58.285391+00:00
-- url     : https://prove2.me/theorems/2dd84dc0-0d41-4083-8791-bcdf1687d086
-- title:
--   Lemma 3.5 — both Bochner identities
-- statement:
--   Let $S>0$, let $W$ satisfy (2.4), and take $f\in D(A)$. If $f$ is even in every coordinate, then
--   $$\mathbb E_\eta[(Af)^2]=\sum_j\mathcal E(\partial_jf)+\mathbb E_\eta\langle\nabla^2W\nabla f,\nabla f\rangle+\sum_j\mathbb E_\eta\!\left[-\frac{c'_j}{X_j}(\partial_jf)^2\right].$$
--   If $f$ is odd only in coordinate $i$, set $g=f/x_i$. Then
--   $$\begin{aligned}\mathbb E_\eta[(Af)^2]={}&\sum_j\mathcal E(\partial_jf)+\mathbb E_\eta\langle\nabla^2W\nabla f,\nabla f\rangle+\sum_{j\ne i}\mathbb E_\eta\!\left[-\frac{c'_j}{X_j}(\partial_jf)^2\right]\\&+\mathbb E_\eta[c_i|\nabla g|^2]+\mathbb E_\eta[(2c_i-X_ic'_i)(\partial_i g)^2]+\mathbb E_\eta\!\left[c_i\frac{W_i}{X_i}g^2\right].\end{aligned}$$
--   Here $c'_j=\partial_jc_j$ and $W_i=\partial_iW$. Every displayed integrand is integrable. Weak derivatives and almost-everywhere parities give the operator-domain interpretation justified by Lemma A.4; smooth compactly supported tests are included. Both exact identities are retained, including every coefficient and the final potential term.
--
--   Differences from the source:
--   - encoding: functions on real Euclidean space with the paper’s analytic domains → Fin n coordinates, L² equivalence classes and canonical graph/form completions; extended nonnegative infima; reason: these represent the same objects; positive dimensions are retained and finite integrals are guarded
--   - encoding: test functions in Lemma 3.5, extended in Lemma A.4 → identities on the full operator domain with the specified parities; reason: Appendix A.4 explicitly supplies this domain and its integrability; no eigenfunction regularity is assumed
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), p. 20, Lemma 3.5; contextual domains in Appendix A, pp. 31–38. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Domains

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl
theorem lemma_3_5 {n : ℕ} (hn : 0 < n) (S : ℝ) (W : Fn n)
    (hS : 0 < S) (hW : Admissible W) :
    (∀ f : Fn n, OperatorDomain S W f → Even (eta S W) f →
      BochnerIntegrable S W f ∧ evenBochner S W f) ∧
    (∀ (f : Fn n) (i : Fin n), OperatorDomain S W f → OneOdd (eta S W) f i →
      BochnerIntegrable S W f ∧ OddIntegrable S W f i ∧ oddBochner S W f i) := by sorry
end UnconditionalKLS.Dunkl
