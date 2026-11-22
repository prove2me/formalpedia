-- Prove2me | Theorems.Thm_PettisIntegral_setOf_weakIntegral_probabilityMeasure_eq_closure_convexHull
-- name    : PettisIntegral.setOf_weakIntegral_probabilityMeasure_eq_closure_convexHull
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:28.424658+00:00
-- url     : https://prove2.me/theorems/d93feaba-1dce-4f9a-9aa6-1efdbd4fd389
-- title:
--   Theorem C.4.3.2(1) — the weak integrals of a continuous function against Radon probability measures form the closed convex hull of its range in the weak completion, and this set is compact
-- statement:
--   **Weakly closed convex hull of the value set of a continuous vector-valued function (Theorem C.4.3.2(1)).** Let $X$ be a compact Hausdorff space, $E$ a Hausdorff locally convex space over $\mathbb k\in\{\mathbb R,\mathbb C\}$ with continuous dual $E'$, and $f\colon X\to E$ a continuous function. Let $\mathscr M^1_+(X)$ be the set of positive Radon measures on $X$ of total mass $1$. For $\mu\in\mathscr M^1_+(X)$ the function $f$ is weakly $\mu$-integrable, with weak integral $\int_X f\,d\mu\in(E')^*$, the linear form $\varphi\mapsto\int_X\varphi(f(x))\,d\mu(x)$ on $E'$. Then, as subsets of the weak completion $(E')^*$,
--   $$\Bigl\{\int_X f(x)\,d\mu(x)\ :\ \mu\in\mathscr M^1_+(X)\Bigr\}=\overline{\mathrm{ch}}\bigl(f(X)\bigr),$$
--   where $\overline{\mathrm{ch}}(f(X))$ is the closure in $(E')^*$, for the topology $\sigma((E')^*,E')$, of the convex hull of the image of $f$ (transported to $(E')^*$ by the canonical map $\iota_E$). Moreover this set is compact for $\sigma((E')^*,E')$.
--
--   So every point of the weakly closed convex hull of a continuous image of a compact space is a barycentre of a Radon probability measure, and conversely. Together with the Mean-Value Theorem this is the mechanism behind the existence of vector-valued integrals: when the closed convex hull of $f(X)$ in $E$ is already compact (for instance when $E$ is quasi-complete), all these barycentres lie in $E$.
--
--   **Formalization Note.** `weakIntegral 𝕜 μ f` and `toWeakCompletion 𝕜` are from `Def_PettisIntegral_Basic`: elements of the weak completion are functions `StrongDual 𝕜 E → 𝕜`, and closure and compactness are taken in this function space with the product topology; this agrees with closure and compactness in $(E')^*$ for $\sigma((E')^*,E')$, since the linear forms are a closed subspace of the product. $\mathscr M^1_+(X)$ is the set of measures $\mu$ on the Borel $\sigma$-algebra of $X$ with `IsProbabilityMeasure μ ∧ μ.Regular`. The convex hull is `convexHull ℝ`. "Hausdorff locally convex" is `[IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]`. The source works over $\mathbb C$ and notes that the real case is in Bourbaki; the statement covers both. Part (2) of the theorem (complex measures of norm at most $1$ and the closed convex circled hull) is not included.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 711-712, Theorem C.4.3.2(1); classical reference: J. Voigt, A Course on Topological Vector Spaces, Birkhäuser, 2020, Proposition 14.4 (cited by the paper for the complex case), and N. Bourbaki, Elements of Mathematics, Integration I, Springer, Ch. III, §3, Prop. 5 (cited by the paper for the real case)

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

namespace PettisIntegral

/-- For a continuous function `f` on a compact Hausdorff space with values in a Hausdorff locally
convex space, the set of weak integrals of `f` against Radon probability measures is the closure,
in the weak completion, of the convex hull of the image of `f`; this set is compact. -/
theorem setOf_weakIntegral_probabilityMeasure_eq_closure_convexHull {𝕜 E X : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (f : X → E) (hf : Continuous f) :
    {a : StrongDual 𝕜 E → 𝕜 | ∃ μ : Measure X, IsProbabilityMeasure μ ∧ μ.Regular ∧
        a = weakIntegral 𝕜 μ f} =
      closure (convexHull ℝ (Set.range fun x : X => toWeakCompletion 𝕜 (f x))) ∧
    IsCompact (closure (convexHull ℝ (Set.range fun x : X => toWeakCompletion 𝕜 (f x)))) := by
  sorry

end PettisIntegral
