-- Prove2me | Theorems.Thm_WhitneyEmbedding_injective_immersion_of_self_transverse_immersion
-- name    : WhitneyEmbedding.injective_immersion_of_self_transverse_immersion
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-11T17:17:16.559212+00:00
-- url     : https://prove2.me/theorems/5fe3031b-a682-4c5f-8144-7514e099374e
-- title:
--   Whitney trick: removing the double points of a self-transverse immersion, $n \ge 3$
-- statement:
--   Let $n\ge 3$ and let $M$ be a Hausdorff, second-countable smooth real $n$-manifold without boundary. Suppose $f:M\to\mathbb R^{2n}$ is a smooth map which is
--
--   1. proper,
--   2. an immersion, i.e. $df_x$ is injective for every $x\in M$, and
--   3. self-transverse, i.e. whenever $x\ne y$ and $f(x)=f(y)$ one has
--   $$\operatorname{im}(df_x)+\operatorname{im}(df_y)=\mathbb R^{2n}.$$
--
--   Then $M$ admits a smooth map
--   $$g:M\longrightarrow\mathbb R^{2n}$$
--   which is proper, injective, and again an immersion.
--
--   In words: in dimensions $n\ge3$ the double points of a self-transverse proper immersion of an $n$-manifold in $\mathbb R^{2n}$ can be removed, leaving a proper injective immersion. This is the Whitney trick stage of the strong Whitney embedding theorem: transverse double points come in pairs that can be cancelled by an isotopy supported near an embedded Whitney disc, which exists precisely because $2n\ge 6$ leaves enough room for the disc to be embedded and its interior to be disjoint from the image. The statement is asserted for arbitrary such $M$, so it covers non-compact, disconnected and non-orientable manifolds; the resulting map $g$ need not be a perturbation of $f$.
--
--   **Formalization Note** Only the existence of $g$ is asserted, with properness stated as `IsProperMap`; combined with injectivity this upgrades $g$ to a topological embedding by a separate point-set lemma.
-- source:
--   H. Whitney, The self-intersections of a smooth n-manifold in 2n-space, Ann. of Math. 45 (1944), pp. 220-246. See also MIT 18.965 Lectures 21-22, Theorem 19.1 and Proposition 19.4, pp. 48-51, https://ocw.mit.edu/courses/18-965-geometry-of-manifolds-fall-2004/d0598b3b5ced2d2d0a9884ee14abeae3_lecture21_22.pdf . This is Theorem 19.1 together with Proposition 19.4 of the MIT notes (the Whitney trick), stated for a proper self-transverse immersion of an arbitrary n-manifold with 2n >= 6.

import Mathlib
open Function Filter Module Set Topology
open scoped Manifold ContDiff

theorem WhitneyEmbedding.injective_immersion_of_self_transverse_immersion (n : ℕ) (hn : 3 ≤ n)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f) (hfp : IsProperMap f)
    (hfd : ∀ x, Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f x))
    (hft : ∀ x y, x ≠ y → f x = f y →
      Submodule.span ℝ
        ((Set.range (mfderiv (𝓡 n) (𝓡 (2 * n)) f x) ∪
          Set.range (mfderiv (𝓡 n) (𝓡 (2 * n)) f y) :
            Set (EuclideanSpace ℝ (Fin (2 * n))))) = ⊤) :
    ∃ g : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ g ∧ Injective g ∧ IsProperMap g ∧
      ∀ x, Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) g x) := by sorry
