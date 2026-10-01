-- Prove2me | Theorems.Thm_PughClosingLemma_general_density_theorem
-- name    : PughClosingLemma.general_density_theorem
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:45:34.541251+00:00
-- url     : https://prove2.me/theorems/0fbd411c-102f-4a27-b223-721de6723a6b
-- title:
--   Pugh's General Density Theorem: $\overline{\mathrm{Per}(g)}=\Omega(g)$ for $C^1$-generic $g$
-- statement:
--   Let $M$ be a compact smooth manifold (Hausdorff, without boundary, of dimension $d$). There is a **residual** subset $\mathcal G\subseteq\mathrm{Diff}^1(M)$ (one containing a countable intersection of open dense sets, for the $C^1$ topology) such that every $g\in\mathcal G$ satisfies
--
--   $$\overline{\mathrm{Per}(g)}=\Omega(g),$$
--
--   where $\mathrm{Per}(g)=\{y : \exists n\ge 1,\ g^n(y)=y\}$ and $\Omega(g)$ is the nonwandering set.
--
--   This is the \"General Density Theorem\" in the title of the cited reference [1]; the closing lemma is its main ingredient.
--
--   **Formalization Note** $\mathrm{Diff}^1(M)$ and its $C^1$ topology are those of `BCWCentralizer_Basic`; \"residual\" is Mathlib's `residual` filter for that topology.
-- source:
--   C. C. Pugh, "An Improved Closing Lemma and a General Density Theorem", Amer. J. Math. 89 (4) (1967), 1010-1021, https://doi.org/10.2307/2373414 (the General Density Theorem named in the title; reference [1] of the uploaded Wikipedia article). Exact theorem number in the paper not verified by the drafter.

import Mathlib
import Definitions.Def_PughClosingLemma_nonwandering
import Definitions.Def_BCWCentralizer_Basic

open scoped Manifold ContDiff Topology

namespace PughClosingLemma

theorem general_density_theorem {d : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) ∞ M] :
    ∃ 𝒢 ∈ @residual (BCWCentralizer.Diff1 d M) BCWCentralizer.c1Topology,
      ∀ g ∈ 𝒢, closure (Function.periodicPts g) = nonwanderingSet g := by sorry

end PughClosingLemma
