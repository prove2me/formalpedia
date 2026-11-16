-- Prove2me | Theorems.Thm_SketchAttr_LOO_Supplement_lemma_C_2
-- name    : SketchAttr.LOO.Supplement.lemma_C_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:52:37.298095+00:00
-- url     : https://prove2.me/theorems/eac20c35-2145-487c-b722-774eea8240c4
-- title:
--   Lemma C.2 — adaptive Gaussian Gram diagonal lower bound
-- statement:
--   There are universal constants $b,\beta>0$ and an integer $L\ge1$. For every $n\ge1$, draw a matrix $G\in\mathbb R^{Ln\times n}$ with independent standard real Gaussian entries, independently of a procedure's arbitrary random seed. Any randomized adaptive procedure using a worst-case budget of $q\le bn$ real matrix-vector queries to $G^\top G$ satisfies
--
--   $$\Pr_{G,\mathrm{seed}}\!\left(\sum_{i=1}^n|\widehat L_i-(G^\top G)_{ii}|^2<\beta n^2\right)\le\frac14.$$
--
--   The procedure sees only its seed and oracle answers, and has unrestricted computation between queries. This is the hard-distribution ingredient for Lemma 5.2.
--
--   Differences from the source:
--   - encoding: indices in [n] and probabilities over random seeds → indices in Fin n and an arbitrary measurable seed probability space; reason: zero-based labels and explicit probability laws change no instance
--   - encoding: at most bn adaptive real matrix-vector queries, with seed independent of G → a q-step measurable transcript with q at most bn and the product of the Gaussian matrix law and seed law; reason: padding permits early stopping and the product law states independence explicitly
-- source:
--   Chris Liaw, Aranyak Mehta, Grigoris Velegkas, Felix Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (October 2026), PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2, p. 29, Lemma C.2

import Mathlib
import Definitions.Def_SketchAttr_LOO_Supplement_Quadratic

open MeasureTheory
open scoped ENNReal

namespace SketchAttr.LOO.Supplement

theorem lemma_C_2 :
    ∃ b β : ℝ, 0 < b ∧ 0 < β ∧ ∃ L : ℕ, 1 ≤ L ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (Seed : Type) [MeasurableSpace Seed]
        (μ : Measure Seed) [IsProbabilityMeasure μ] (q : ℕ)
        (P : MatrixProcedure Seed n q), (q : ℝ) ≤ b * n →
      ((realGaussianMatrix (L*n) n).prod μ)
        {Gs | squaredDiagonalError (matrixEstimate P (gram Gs.1) Gs.2) (gram Gs.1) <
          β * (n : ℝ)^2} ≤ (1/4 : ℝ≥0∞) := by sorry

end SketchAttr.LOO.Supplement
