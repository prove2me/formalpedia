-- Prove2me | Theorems.Thm_RecGaussColoring_Main_lemma_1_3
-- name    : RecGaussColoring.Main.lemma_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:14.563593+00:00
-- url     : https://prove2.me/theorems/214340ce-b9fe-4b40-a670-168b323ebff5
-- title:
--   Lemma 1.3 — expectation or local covers
-- statement:
--   Let $G$ be any $n$-vertex graph, $v_i\in\mathbb R^d$ any strict vector three-coloring, $t>0$, and $M$ any selector of maximal matchings of induced subgraphs. If $I$ is the KMS′ output, at least one alternative holds:
--   $$
--   \mathbb E|I|\ge\frac n4\Phi^c(t),\qquad\text{or}\qquad
--   \exists\varnothing\ne W\subseteq V\ \forall i\in W:\
--   \{u_{j\mid i}:j\in N_{G[W]}(i)\}\text{ is a }(\sqrt3t,1/8)\text{-cover}.
--   $$
--   This dichotomy supplies the failure subgraph analyzed by the certificate lemmas. No special selector is chosen.
--
--   Differences from the source:
--   - encoding: finite Euclidean families and labelled finite graphs → Fin n vertices and EuclideanSpace ℝ (Fin d); reason: relabelling preserves every finite instance and dimension
--   - encoding: Algorithm 2 uses an arbitrary maximal matching and its expected output size → every valid matching selector, with expectation as a finite sum over selected vertex sets; reason: a selector specifies the matching choice for every possible selected set; the finite distribution is the same Gaussian rounding law
-- source:
--   Ijay Narang, Yukai Tang, STOC 2027 submission #295 (October 2026), Lemma 1.3, p. 4. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/295.pdf

import Definitions.Def_RecGaussColoring_Main_Rounding

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

namespace RecGaussColoring.Main

/-- Lemma 1.3, p. 4; every maximal-matching selector is covered. -/
theorem lemma_1_3 (I : Graph3) (d : ℕ) (v : Fin I.n → Space d)
    (hv : StrictVectorColoring I.G v) (t : ℝ) (ht : 0 < t)
    (M : MatchingSelector I) (hM : ValidSelector I M) :
  (I.n : ℝ)/4 * PhiTail t ≤ kmsExpectation I v t M ∨
    ∃ W : Finset (Fin I.n), W.Nonempty ∧ LocalCovers I v W t := by sorry

end RecGaussColoring.Main
