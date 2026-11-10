-- Prove2me | Theorems.Thm_UnconditionalKLS_Dunkl_lemma_3_1
-- name    : UnconditionalKLS.Dunkl.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T20:08:37.568952+00:00
-- url     : https://prove2.me/theorems/c517c224-c3e8-41a4-807c-739f3cdf6b51
-- title:
--   Lemma 3.1 — Dirichlet identity and symmetry
-- statement:
--   Fix $S>0$ and an unconditional $C^2$ potential $W$ satisfying (2.4), with auxiliary law $\eta$. The closure $A$ and its completed form satisfy
--   $$\langle g,Af\rangle_{L^2(\eta)}=\mathcal E(g,f)\quad(f\in D(A),\ g\in D(A^{1/2})),\qquad\langle g,Af\rangle=\langle Ag,f\rangle\quad(f,g\in D(A)).$$
--   These are the integration-by-parts identity and symmetry, respectively. The domain convention is the full extension explicitly stated on p.36, immediately before Lemma A.3. Inner products have their actual $L^2$ integral meaning and are finite. This provides both displayed conclusions, including the form identity for a form-domain second test.
--
--   Differences from the source:
--   - encoding: functions on real Euclidean space with the paper’s analytic domains → Fin n coordinates, L² equivalence classes and canonical graph/form completions; extended nonnegative infima; reason: these represent the same objects; positive dimensions are retained and finite integrals are guarded
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), p. 15, Lemma 3.1; contextual domains in Appendix A, pp. 31–38. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Domains

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl
theorem lemma_3_1 {n : ℕ} (hn : 0 < n) (S : ℝ) (W : Fn n)
    (hS : 0 < S) (hW : Admissible W) :
    (∀ f g : Fn n, OperatorDomain S W f → FormDomain S W g →
      inner ℝ (l2 (eta S W) g) (action S W f) = form S W g f) ∧
    (∀ f g : Fn n, OperatorDomain S W f → OperatorDomain S W g →
      inner ℝ (l2 (eta S W) g) (action S W f) =
        inner ℝ (action S W g) (l2 (eta S W) f)) := by sorry
end UnconditionalKLS.Dunkl
