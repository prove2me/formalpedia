-- Prove2me | Theorems.Thm_UnconditionalKLS_Dunkl_lemma_3_2
-- name    : UnconditionalKLS.Dunkl.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T20:08:39.754229+00:00
-- url     : https://prove2.me/theorems/d2cd8304-6b7b-4045-8065-5f1f8147d4b1
-- title:
--   Lemma 3.2 — Hardy comparison and both Poincaré bounds
-- statement:
--   Let $S>0$ and let $W$ satisfy (2.4). Write $\eta$ for the auxiliary law, $\mathcal E$ for its completed Dunkl form and $\lambda$ for its Rayleigh gap. For every $f$ in the form domain, its weak gradient and weighted differences are square integrable and
--   $$\mathcal E(f)=\mathbb E_\eta|\nabla f|^2+\sum_j\mathbb E_\eta[c_j(D_jf)^2]\le9\mathbb E_\eta|\nabla f|^2,\qquad\frac1\lambda\le C_P(\eta)\le\frac9\lambda.$$
--   The estimate compares the modified and ordinary energies while retaining both consequences for the optimal constant. The form-domain formulation uses the completion and extension in Appendix A, including the paragraph following the proof of Lemma A.2; it includes legitimate smooth tests and the locally Lipschitz finite-energy tests through Lemma A.2.
--
--   Differences from the source:
--   - encoding: functions on real Euclidean space with the paper’s analytic domains → Fin n coordinates, L² equivalence classes and canonical graph/form completions; extended nonnegative infima; reason: these represent the same objects; positive dimensions are retained and finite integrals are guarded
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), p. 16, Lemma 3.2; contextual domains in Appendix A, pp. 31–38. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Domains

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl
theorem lemma_3_2 {n : ℕ} (hn : 0 < n) (S : ℝ) (W : Fn n)
    (hS : 0 < S) (hW : Admissible W) :
    (∀ f : Fn n, FormDomain S W f →
      WeaklyDifferentiable f ∧ Integrable (fun x => ‖weakGrad f x‖^2) (eta S W) ∧
      (∀ j, Integrable (fun x => cj S j x * (difference f j x)^2) (eta S W)) ∧
      energy S W f = (∫ x, ‖weakGrad f x‖^2 ∂eta S W) +
        ∑ j, ∫ x, cj S j x * (difference f j x)^2 ∂eta S W ∧
      energy S W f ≤ 9 * ∫ x, ‖weakGrad f x‖^2 ∂eta S W) ∧
    (gap S W)⁻¹ ≤ poincare (eta S W) ∧
    poincare (eta S W) ≤ 9 * (gap S W)⁻¹ := by sorry
end UnconditionalKLS.Dunkl
