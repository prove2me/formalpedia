-- Prove2me | Theorems.Thm_PughClosingLemma_pugh_closing_lemma
-- name    : PughClosingLemma.pugh_closing_lemma
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:49:43.018365+00:00
-- url     : https://prove2.me/theorems/9baa6595-5aa2-49a4-9841-3bc12c2c4e53
-- title:
--   Pugh's closing lemma
-- statement:
--   Let $M$ be a compact smooth manifold (Hausdorff, without boundary, of dimension $d$) and let $f\colon M\to M$ be a $C^1$ diffeomorphism. Let $x\in M$ be a **nonwandering point** of $f$: for every neighbourhood $U$ of $x$ there is $n\ge 1$ with $f^n(U)\cap U\neq\emptyset$. Then there are diffeomorphisms arbitrarily close to $f$ in the $C^1$ topology of $\mathrm{Diff}^1(M)$ for which $x$ is a periodic point:
--
--   $$\forall\,\mathcal U\ni f \text{ a } C^1\text{-neighbourhood in } \mathrm{Diff}^1(M),\quad \exists\, g\in\mathcal U,\ \exists\, n\ge 1:\ g^n(x)=x .$$
--
--   The closing lemma says that recurrence of the weakest kind (nonwandering) can be turned into genuine periodicity by a $C^1$-small perturbation. It is the key ingredient of Pugh's General Density Theorem.
--
--   **Formalization Note** $\mathrm{Diff}^1(M)$ and its $C^1$ topology come from the published definition file `BCWCentralizer_Basic`: $\mathrm{Diff}^1(M)$ is `M ≃ₘ^1⟮𝓡 d, 𝓡 d⟯ M`, and the topology is induced by $g\mapsto Tg\in C(TM,TM)$ with the compact-open topology, which on a compact manifold is the usual $C^1$ topology. \"Smooth\" is encoded as a $C^\infty$ atlas modelled on $\mathbb R^d$; \"arbitrarily close\" as membership in every neighbourhood; periodicity requires a period $n\ge 1$.
-- source:
--   Wikipedia, "Pugh's closing lemma", section "Formal statement" (revision oldid=1304222873, https://en.wikipedia.org/w/index.php?title=Pugh%27s_closing_lemma&oldid=1304222873), citing C. C. Pugh, "An Improved Closing Lemma and a General Density Theorem", Amer. J. Math. 89 (4) (1967), 1010-1021, https://doi.org/10.2307/2373414. Wikipedia section "Formal statement" (the only displayed statement of the article).

import Mathlib
import Definitions.Def_PughClosingLemma_nonwandering
import Definitions.Def_BCWCentralizer_Basic

open scoped Manifold ContDiff Topology

namespace PughClosingLemma

theorem pugh_closing_lemma {d : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) ∞ M]
    (f : BCWCentralizer.Diff1 d M) (x : M) (hx : IsNonwandering f x) :
    ∀ 𝒰 ∈ @nhds (BCWCentralizer.Diff1 d M) BCWCentralizer.c1Topology f,
      ∃ g ∈ 𝒰, x ∈ Function.periodicPts g := by sorry

end PughClosingLemma
