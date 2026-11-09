-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_lemma_18
-- name    : TFIMPhaseDiagram.Classical.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:04:24.604001+00:00
-- url     : https://prove2.me/theorems/d8725698-f88e-4da3-a8d4-e7578c89a9fd
-- title:
--   Lemma 18 — Closed-cycle entrywise covariance bound, both inequalities
-- statement:
--   For a cycle of $M\ge3$ spins with arbitrary finite fields, suppose $b>0$ and $|K_k|\le b$ for every edge. Put $a=\tanh b$, and for $i\le j$ let $A,B$ be the absolute products of $\tanh K_k$ along the two complementary arcs. Then both inequalities hold:
--   $$|\operatorname{Cov}(\pi_{K,w})_{i,j}|\le\frac{A+B}{1+|\prod_k\tanh K_k|}\le\frac{a^{j-i}+a^{M-(j-i)}}{1+a^M}.$$
--   Signed couplings and the case $i=j$ are retained. The row sums of these bounds control the covariance operator norm.
--
--   Differences from the source:
--   - encoding: the two arcs between i and j on a cycle → zero-based filtered products and natural lengths under i<=j; reason: Both source inequalities and the diagonal case are retained.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, printed p.11 = PDF p.11, Lemma 18

import Definitions.Def_TFIMPhaseDiagram_Classical_traceSetup

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
/-- Lemma 18, pp.11-12; both arcs, both inequalities, i=j included. -/
theorem lemma_18 (M : ℕ) (hM : 3 ≤ M) (K : Fin M → ℝ) (w : Fin M → ℝ)
    (b : ℝ) (hb : 0 < b) (hK : ∀ k, |K k| ≤ b) (i j : Fin M) (hij : i ≤ j) :
  |spinCov (cycleProb K (fun k => .finite (w k))) i j| ≤
    (|arcProduct K i j| + |otherArcProduct K i j|) / (1 + |∏ k, Real.tanh (K k)|) ∧
  (|arcProduct K i j| + |otherArcProduct K i j|) / (1 + |∏ k, Real.tanh (K k)|) ≤
    ((Real.tanh b)^(j.val-i.val) + (Real.tanh b)^(M-(j.val-i.val))) /
      (1 + (Real.tanh b)^M) := by sorry
end TFIMPhaseDiagram.Classical
