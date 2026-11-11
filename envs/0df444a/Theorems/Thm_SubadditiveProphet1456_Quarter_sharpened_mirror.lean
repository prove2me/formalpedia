-- Prove2me | Theorems.Thm_SubadditiveProphet1456_Quarter_sharpened_mirror
-- name    : SubadditiveProphet1456.Quarter.sharpened_mirror
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:57.792446+00:00
-- url     : https://prove2.me/theorems/cb71f58b-ddfb-4746-862d-3623d9322129
-- title:
--   Lemma 3.2 — Conditional sharpened mirror lemma for arbitrary RSGs
-- statement:
--   Let each support valuation have any Borel probability law on nonnegative real score vectors, with arbitrary coordinate correlations and no discreteness or boundedness restriction. For a fixed buyer $i$, fixed type $\tau$, and fixed score vector $b$, let $Y,Z$ be independent full reference profiles from the same type and score laws. Define
--   $$
--   S=\{j:b_j>p_j(Y)\ge H_{ij}(Z)\},\qquad
--   W=\{j:b_j>\Theta_{ij}(Y,Z)\}.
--   $$
--   Then
--   $$
--   \mathbb E[v_{i,\tau}(S)]\ge\tfrac12\mathbb E[v_{i,\tau}(W)].
--   $$
--   The prefix of $Z$ has the law of the independent actual predecessor scores. Fixing $(v_i,\xi_i)$ fixes $(\tau,b)$, so this pointwise statement gives the source's conditional inequality, including nonatomic private randomness. These bounded welfare functions are integrable although the scores themselves need not be.
--
--   This lemma applies to every random score generator, and does not presuppose the capped construction or a value-retention claim.
--
--   Differences from the source:
--   - encoding: Finite items and nonempty finite buyer type supports in fixed arrival order → Zero-based Fin indices and type supports Fin (k+1), with positive type probabilities; reason: Relabeling covers every source instance, including empty item or buyer sets; zero-probability labels are omitted from support
--   - generalization: The conditional comparison given the realized valuation and private score randomness → The comparison for every fixed supported valuation and every fixed nonnegative score vector; reason: The source proof is a pointwise argument after conditioning; substituting the score determined by the private randomness gives the a.e. conditional comparison without requiring atoms
-- source:
--   Twan Kroll, Calum MacRury, Rebecca Reiffenhäuser, Siddharth M. Sundaram, STOC 2027 submission #1456 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1456.pdf, printed p.10, PDF p.11, Lemma 3.2.

import Definitions.Def_SubadditiveProphet1456_Quarter_CapHeight
import Definitions.Def_SubadditiveProphet1456_Quarter_Machine

open scoped BigOperators NNReal ENNReal
open MeasureTheory

namespace SubadditiveProphet1456.Quarter

theorem sharpened_mirror
    (n m : ℕ) (I : Instance n m)
    (φ : (i : Fin n) → Fin (I.types i+1) → Measure (Score m))
    (hφ : ∀ i t, IsProbabilityMeasure (φ i t))
    (i : Fin n) (t : Fin (I.types i+1)) (b : Score m) :
    (1/2:ℝ) * (∫ Y, ∫ Z, I.valuation i t (mirrorSet i b Y Z)
      ∂(referenceMeasure I φ) ∂(referenceMeasure I φ)) ≤
    ∫ Y, ∫ Z, I.valuation i t (allocated i b Y Z)
      ∂(referenceMeasure I φ) ∂(referenceMeasure I φ) := by sorry

end SubadditiveProphet1456.Quarter
