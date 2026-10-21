-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P32_sequentialLimits_continuousExtension
-- name    : QAlgorithms.Papers.Independent.Renew46.P32.sequentialLimits_continuousExtension
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:12:24.530797+00:00
-- url     : https://prove2.me/theorems/25efebc8-595d-4f74-9582-a7687a97602d
-- title:
--   Continuous extension from convergent sequences
-- statement:
--   Let $X$ be a Hausdorff metrizable topological space, $Y$ a Hausdorff regular topological space, $D\subseteq X$ dense, and $f:D\to Y$ continuous. Suppose that for every sequence $(x_n)$ in $D$ which converges in $X$, the sequence $(f(x_n))$ has a limit in $Y$. Then there exists a continuous $g:X\to Y$ such that
--   $$g|_D=f.$$
--
--   The extension takes values in $Y$ itself, without a completeness assumption. This is the source's sequential extension criterion.
-- source:
--   Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields, arXiv:math/0303300v1, PDF p. 50, Lemma 10.6

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

namespace QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

/-- Lemma 10.6, PDF p. 50: all limits and the extension take values in Y,
not in its completion. Hausdorffness is the Part III standing convention. -/
theorem sequentialLimits_continuousExtension
    {X : Type u} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [T2Space X]
    {Y : Type v} [TopologicalSpace Y] [RegularSpace Y] [T2Space Y]
    (D : Set X) (hD : Dense D) (f : D → Y) (hf : Continuous f)
    (hLimits : ∀ (s : ℕ → D) (x : X),
      Tendsto (fun n => (s n : X)) atTop (𝓝 x) →
        ∃ y : Y, Tendsto (fun n => f (s n)) atTop (𝓝 y)) :
    ∃ g : X → Y, Continuous g ∧ ∀ x : D, g x = f x := by sorry

end QAlgorithms.Papers.Independent.Renew46.P32
