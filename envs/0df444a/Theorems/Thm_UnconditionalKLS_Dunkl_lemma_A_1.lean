-- Prove2me | Theorems.Thm_UnconditionalKLS_Dunkl_lemma_A_1
-- name    : UnconditionalKLS.Dunkl.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T20:08:52.097623+00:00
-- url     : https://prove2.me/theorems/b286a3b7-da72-4119-9610-9aea93ab85aa
-- title:
--   Lemma A.1 — actual operator closure and spectrum
-- statement:
--   Let $n\ge1$, $S>0$ and let $W$ satisfy (2.4). Start the actual Dunkl expression (3.3), with its paired Taylor extension, on $C_c^\infty(\mathbb R^n)$ in $L^2(\eta)$. Its graph closure is single valued, densely defined, self-adjoint and nonnegative, and
--   $$\operatorname{ker}A=\{\text{constant functions}\},\qquad (A+I)^{-1}\text{ is compact}.$$
--   The compact-resolvent condition expresses the discrete spectrum established in the source. The completed gradient/difference graph is also single valued, so it supplies the actual closed form rather than an arbitrary chosen energy. These conclusions establish the analytic realization needed to speak about the first eigenfunction. No spectral property is present in the input definition of the potential.
--
--   Differences from the source:
--   - encoding: functions on real Euclidean space with the paper’s analytic domains → Fin n coordinates, L² equivalence classes and canonical graph/form completions; extended nonnegative infima; reason: these represent the same objects; positive dimensions are retained and finite integrals are guarded
--   - encoding: discrete spectrum and the associated form of the closure → compact resolvent at -1 and single-valued completed form graph; reason: the proof on p.34 establishes compact resolvent, and the form realization is justified on pp.35–36
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), p. 32, Lemma A.1; contextual domains in Appendix A, pp. 31–38. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Domains

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl
theorem lemma_A_1 {n : ℕ} (hn : 0 < n) (S : ℝ) (W : Fn n)
    (hS : 0 < S) (hW : Admissible W) :
    SelfAdjointGraph S W ∧
    (∀ u v, (u,v) ∈ operatorGraph S W → 0 ≤ inner ℝ v u) ∧
    CompactResolvent S W ∧
    (∀ u : Hilbert (eta S W), (u,0) ∈ operatorGraph S W ↔
      ∃ a : ℝ, u = l2 (eta S W) (fun _ => a)) ∧
    (∀ u v w, (u,v) ∈ formGraph S W → (u,w) ∈ formGraph S W → v = w) := by sorry
end UnconditionalKLS.Dunkl
