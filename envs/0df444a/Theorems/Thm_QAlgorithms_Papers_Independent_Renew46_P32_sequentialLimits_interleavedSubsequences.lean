-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P32_sequentialLimits_interleavedSubsequences
-- name    : QAlgorithms.Papers.Independent.Renew46.P32.sequentialLimits_interleavedSubsequences
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:13:28.367558+00:00
-- url     : https://prove2.me/theorems/1ef857e9-e41c-46a7-9fe3-b34a52c36ff3
-- title:
--   Interleaved subsequences and existence of limits
-- statement:
--   Let $X$ be a Hausdorff metrizable space, $Y$ a Hausdorff topological space, $S\subseteq X$, $x\in\overline S$, and $f:S\to Y$ any map. The following are equivalent:
--
--   1. For every sequence $(x_n)$ in $S$ converging to $x$, the sequence $(f(x_n))$ converges in $Y$.
--   2. For every pair $(x_n),(y_n)$ in $S$ converging to $x$, there are strictly increasing index maps $i,j:\mathbb N\to\mathbb N$ such that
--   $$f(x_{i(0)}),f(y_{j(0)}),f(x_{i(1)}),f(y_{j(1)}),\ldots$$
--   converges in $Y$.
--
--   This criterion requires no continuity of $f$ and allows $x\notin S$.
-- source:
--   Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields, arXiv:math/0303300v1, PDF p. 51, Lemma 10.8

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

namespace QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

/-- Lemma 10.8, PDF p. 51: x is in closure(S), not necessarily S.
No continuity hypothesis on f is imposed. -/
theorem sequentialLimits_interleavedSubsequences
    {X : Type u} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [T2Space X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    (S : Set X) (f : S → Y) (x : X) (hx : x ∈ closure S) :
    (∀ a : ℕ → S, Tendsto (fun n => (a n : X)) atTop (𝓝 x) →
      ∃ y : Y, Tendsto (fun n => f (a n)) atTop (𝓝 y)) ↔
    (∀ a b : ℕ → S,
      Tendsto (fun n => (a n : X)) atTop (𝓝 x) →
      Tendsto (fun n => (b n : X)) atTop (𝓝 x) →
      ∃ i j : ℕ → ℕ, StrictMono i ∧ StrictMono j ∧
        ∃ y : Y, Tendsto (alternatingSequence (fun n => f (a (i n)))
          (fun n => f (b (j n)))) atTop (𝓝 y)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P32
