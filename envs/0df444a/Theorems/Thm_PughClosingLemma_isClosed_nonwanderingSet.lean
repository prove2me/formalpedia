-- Prove2me | Theorems.Thm_PughClosingLemma_isClosed_nonwanderingSet
-- name    : PughClosingLemma.isClosed_nonwanderingSet
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T21:20:57.376014+00:00
-- url     : https://prove2.me/theorems/b411cfe2-5eae-46c5-b411-903cb7100d3f
-- title:
--   The nonwandering set $\Omega(f)$ is closed
-- statement:
--   Let $X$ be a topological space and $f\colon X\to X$ any map. Then the nonwandering set $\Omega(f)$ is a closed subset of $X$.
--
--   Together with $\mathrm{Per}(f)\subseteq\Omega(f)$ this gives $\overline{\mathrm{Per}(f)}\subseteq\Omega(f)$, the easy half of the equality asserted for generic diffeomorphisms by the General Density Theorem.
-- source:
--   Standard property of the nonwandering set (not stated separately in the source article); context: Wikipedia, "Pugh's closing lemma", section "Formal statement" (revision oldid=1304222873, https://en.wikipedia.org/w/index.php?title=Pugh%27s_closing_lemma&oldid=1304222873), citing C. C. Pugh, "An Improved Closing Lemma and a General Density Theorem", Amer. J. Math. 89 (4) (1967), 1010-1021, https://doi.org/10.2307/2373414

import Mathlib
import Definitions.Def_PughClosingLemma_nonwandering

open scoped Topology

namespace PughClosingLemma

theorem isClosed_nonwanderingSet {X : Type*} [TopologicalSpace X] (f : X → X) :
    IsClosed (nonwanderingSet f) := by sorry

end PughClosingLemma
