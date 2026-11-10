-- Prove2me | Theorems.Thm_UnconditionalKLS_Dunkl_lemma_A_4
-- name    : UnconditionalKLS.Dunkl.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T20:08:37.702795+00:00
-- url     : https://prove2.me/theorems/ce3385aa-3ddc-44ae-a75d-c8cb17a48e90
-- title:
--   Lemma A.4 — extension of derivative and quotient identities
-- statement:
--   Let $S>0$, let $W$ satisfy (2.4), and let $f\in D(A)$. If $f$ is all even, or odd in one coordinate $i$ and even in all others, its weak derivatives obey
--   $$\partial_jf\in D(A^{1/2})\quad\text{for every }j,$$
--   and the corresponding complete identity (3.10) or (3.11) holds with all its integrands integrable. In the one-odd case, $g=f/x_i$ is weakly differentiable on each open orthant and
--   $$\mathbb E_\eta[c_i(g^2+|\nabla g|^2)]<\infty,\qquad\left(\lambda-\frac3{2S^2}\right)\left(\mathbb E_\eta[c_ig^2]-\frac{\mathbb E_\eta[c_ig]^2}{\mathbb E_\eta[c_i]}\right)\le\mathbb E_\eta[c_i|\nabla g|^2].$$
--   All conclusions apply to arbitrary operator-domain representatives of the given parities, including the first eigenfunction; compact support is not an input. The two cases are stated together using the same shared Bochner formulas as Lemma 3.5.
--
--   Differences from the source:
--   - encoding: functions on real Euclidean space with the paper’s analytic domains → Fin n coordinates, L² equivalence classes and canonical graph/form completions; extended nonnegative infima; reason: these represent the same objects; positive dimensions are retained and finite integrals are guarded
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), p. 37, Lemma A.4; contextual domains in Appendix A, pp. 31–38. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Domains

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl
theorem lemma_A_4 {n : ℕ} (hn : 0 < n) (S : ℝ) (W : Fn n)
    (hS : 0 < S) (hW : Admissible W) :
    (∀ f : Fn n, OperatorDomain S W f → Even (eta S W) f →
      WeaklyDifferentiable f ∧ (∀ j, FormDomain S W (weakPartial f j)) ∧
      BochnerIntegrable S W f ∧ evenBochner S W f) ∧
    (∀ (f : Fn n) (i : Fin n), OperatorDomain S W f → OneOdd (eta S W) f i →
      WeaklyDifferentiable f ∧ (∀ j, FormDomain S W (weakPartial f j)) ∧
      BochnerIntegrable S W f ∧ OddIntegrable S W f i ∧ oddBochner S W f i ∧
      WeightedTest S W (quotient f i) i ∧ weightedEstimate S W (quotient f i) i) := by sorry
end UnconditionalKLS.Dunkl
