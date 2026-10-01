-- Prove2me | Theorems.Thm_PughClosingLemma_periodicPts_subset_nonwanderingSet
-- name    : PughClosingLemma.periodicPts_subset_nonwanderingSet
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T21:13:43.571339+00:00
-- url     : https://prove2.me/theorems/6c95d9d3-7bc4-409b-849b-da2b74605b37
-- title:
--   Periodic points are nonwandering: $\mathrm{Per}(f)\subseteq\Omega(f)$
-- statement:
--   Let $X$ be a topological space and $f\colon X\to X$ any map. Every periodic point of $f$ is nonwandering:
--
--   $$\mathrm{Per}(f)=\{x : \exists n\ge 1,\ f^n(x)=x\}\ \subseteq\ \Omega(f).$$
--
--   This is the elementary converse direction to the closing lemma: periodic points are always nonwandering, and the closing lemma says nonwandering points become periodic after a $C^1$-small perturbation.
-- source:
--   Standard property of the nonwandering set (not stated separately in the source article); context: Wikipedia, "Pugh's closing lemma", section "Formal statement" (revision oldid=1304222873, https://en.wikipedia.org/w/index.php?title=Pugh%27s_closing_lemma&oldid=1304222873), citing C. C. Pugh, "An Improved Closing Lemma and a General Density Theorem", Amer. J. Math. 89 (4) (1967), 1010-1021, https://doi.org/10.2307/2373414

import Mathlib
import Definitions.Def_PughClosingLemma_nonwandering

open scoped Topology

namespace PughClosingLemma

theorem periodicPts_subset_nonwanderingSet {X : Type*} [TopologicalSpace X] (f : X → X) :
    Function.periodicPts f ⊆ nonwanderingSet f := by sorry

end PughClosingLemma
