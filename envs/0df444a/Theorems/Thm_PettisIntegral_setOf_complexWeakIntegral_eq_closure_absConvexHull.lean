-- Prove2me | Theorems.Thm_PettisIntegral_setOf_complexWeakIntegral_eq_closure_absConvexHull
-- name    : PettisIntegral.setOf_complexWeakIntegral_eq_closure_absConvexHull
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:25:00.883171+00:00
-- url     : https://prove2.me/theorems/dfa862de-630a-4ce7-a04c-c7c56d4305b0
-- title:
--   Theorem C.4.3.2(2) — integrals against complex Radon measures of norm $\le 1$ fill the weakly closed absolutely convex hull of $f(X)$, which is compact
-- statement:
--   **Weakly closed absolutely convex hull of the value set of a continuous vector-valued function (Theorem C.4.3.2(2)).** Let $E$ be a Hausdorff locally convex space over $\mathbb C$, $X$ a compact Hausdorff space and $f\colon X\to E$ a continuous function. Let $\mathscr M^{\le 1}(X)$ be the set of complex Radon measures $\mu$ on $X$ with $\|\mu\|=|\mu|(X)\le 1$. Then, as subsets of the weak completion $(E')^*$,
--   $$\Bigl\{\int_X f(x)\,d\mu(x)\ :\ \mu\in\mathscr M^{\le 1}(X)\Bigr\}\;=\;\overline{\mathrm{cch}}\bigl(f(X)\cup\{0\}\bigr),$$
--   where $\int_X f\,d\mu\in(E')^*$ is the weak integral $\varphi\mapsto\int_X\varphi(f(x))\,d\mu(x)$ and the right-hand side is the closure, for the topology $\sigma((E')^*,E')$, of the convex circled (absolutely convex) hull of the image of $f$ together with $0$. Moreover this set is compact for $\sigma((E')^*,E')$.
--
--   It is the complex companion of the description of the weakly closed convex hull of $f(X)$ as the set of barycentres $\int_X f\,d\mu$ of Radon probability measures (part (1) of the theorem, published in the positive-measure package). The proof combines the mean value theorem with the weak-$*$ compactness of the unit ball of $\mathscr M(X)=C(X)'$.
--
--   **Formalization Note.** `complexWeakIntegral μ f` is the weak integral against a complex measure from `Def_PettisIntegral_ComplexMeasure`, and `toWeakCompletion ℂ` is $\iota_E$ from `Def_PettisIntegral_Basic`. The weak completion is represented in the product space `StrongDual ℂ E → ℂ`, where closure and compactness are taken. $\mathscr M^{\le1}(X)$ is the set of `μ : ComplexMeasure X` with `μ.variation.Regular` and `μ.variation Set.univ ≤ 1` (Borel $\sigma$-algebra on $X$); since $X$ is compact and $f$ continuous, $f$ is weakly integrable for each of them. The absolutely convex hull of a set $S$ is `convexHull ℝ (balancedHull ℂ S)`. The statement is the conjunction of the equality of sets and the compactness. **Deviation from the source.** $0$ is adjoined to $f(X)$ before taking the hull (`insert 0 …`); this changes nothing when $X\neq\emptyset$, and for $X=\emptyset$ both sides are $\{0\}$, whereas the hull of the empty set is empty.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 711-712, Theorem C.4.3.2(2); classical reference: for part (1), J. Voigt, A Course on Topological Vector Spaces, Birkhäuser, 2020, Prop. 14.4, and over the reals N. Bourbaki, Elements of Mathematics, Integration I, Springer, Ch. III, §3, Prop. 5 (as cited by the paper)

import Mathlib
import Definitions.Def_PettisIntegral_Basic
import Definitions.Def_PettisIntegral_ComplexMeasure

open MeasureTheory

set_option autoImplicit false

namespace PettisIntegral

/-- For a continuous function `f` on a compact Hausdorff space with values in a Hausdorff locally
convex space, the set of weak integrals of `f` against the complex Radon measures of total
variation at most `1` is the closure, in the weak completion, of the absolutely convex hull of the
image of `f` (with `0` adjoined); this set is compact. -/
theorem setOf_complexWeakIntegral_eq_closure_absConvexHull {E X : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (f : X → E) (hf : Continuous f) :
    {a : StrongDual ℂ E → ℂ | ∃ μ : ComplexMeasure X, μ.variation.Regular ∧
        μ.variation Set.univ ≤ 1 ∧ a = complexWeakIntegral μ f} =
      closure (convexHull ℝ (balancedHull ℂ
        (insert 0 (Set.range fun x : X => toWeakCompletion ℂ (f x))))) ∧
    IsCompact (closure (convexHull ℝ (balancedHull ℂ
        (insert 0 (Set.range fun x : X => toWeakCompletion ℂ (f x)))))) := by sorry

end PettisIntegral
