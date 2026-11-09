-- Prove2me | Theorems.Thm_RecGaussColoring_Main_kms_expectation
-- name    : RecGaussColoring.Main.kms_expectation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:28.279465+00:00
-- url     : https://prove2.me/theorems/8fef8e14-204e-4047-9346-5cb39eeadf38
-- title:
--   §3.2, proof of Theorem 1.5, p. 21 — KMS′ expectation
-- statement:
--   For every $0<c<c^\dagger$, there is a single threshold $n_0$ such that for every three-colorable graph $G$ on $n\ge n_0$ vertices with $\Delta(G)\le n^{3(1+c)/(5+3c)}$, every dimension $d$, every strict vector three-coloring into $\mathbb R^d$, every positive threshold $t$ with $\Phi^c(t)=n^{-1/(5+3c)}$, and every maximal-matching selector, one KMS′ trial satisfies
--   $$
--   \mathbb E|I|\ge\frac14 n^{(4+3c)/(5+3c)}.
--   $$
--   The threshold $n_0$ is fixed before the graph, vectors and selector. This is the quantitative expectation bound in the proof, before amplification to a high-probability independent-set algorithm.
--
--   Differences from the source:
--   - encoding: finite Euclidean families and labelled finite graphs → Fin n vertices and EuclideanSpace ℝ (Fin d); reason: relabelling preserves every finite instance and dimension
--   - encoding: for all sufficiently large n in §3.2 → ∃n₀ before every graph, dimension, threshold and selector; reason: this records the proof’s uniform asymptotic conclusion, with t>0 as required by Algorithm 2
-- source:
--   Ijay Narang, Yukai Tang, STOC 2027 submission #295 (October 2026), §3.2, proof of Theorem 1.5, unnumbered display, p. 21. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/295.pdf

import Definitions.Def_RecGaussColoring_Main_Rounding
import Definitions.Def_RecGaussColoring_Main_Parameters

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

namespace RecGaussColoring.Main

/-- §3.2, proof of Theorem 1.5, p. 21; n₀ is uniform over all graphs and dimensions. -/
theorem kms_expectation (c : ℝ) (hc : 0 < c) (hcD : c < cDagger) :
  ∃ n₀ : ℕ, ∀ (I : Graph3), n₀ ≤ I.n → ThreeColorable I →
    (maxDeg I : ℝ) ≤ (I.n : ℝ)^(sparseExponent c) →
    ∀ (d : ℕ) (v : Fin I.n → Space d), StrictVectorColoring I.G v →
      ∀ t : ℝ, 0 < t → PhiTail t = (I.n : ℝ)^(-1/(5+3*c)) →
        ∀ M : MatchingSelector I, ValidSelector I M →
          (1/4 : ℝ) * (I.n : ℝ)^((4+3*c)/(5+3*c)) ≤ kmsExpectation I v t M := by sorry

end RecGaussColoring.Main
