-- Prove2me | Theorems.Thm_PughClosingLemma_nonwanderingSet_nonempty
-- name    : PughClosingLemma.nonwanderingSet_nonempty
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T21:25:34.47928+00:00
-- url     : https://prove2.me/theorems/f71bbafb-f7ac-46ae-9e9d-f3b4a12d6648
-- title:
--   On a nonempty compact space $\Omega(f)\neq\emptyset$
-- statement:
--   Let $X$ be a nonempty compact topological space and $f\colon X\to X$ any map. Then the nonwandering set $\Omega(f)$ is nonempty.
--
--   This guarantees that the hypothesis of the closing lemma is never vacuous: every diffeomorphism of a nonempty compact manifold has nonwandering points.
--
--   **Formalization Note** The statement is usually quoted for continuous $f$; continuity is not needed, so the Lean statement omits it (it is a stronger, still true statement). No Hausdorff assumption is made.
-- source:
--   Standard property of the nonwandering set (not stated separately in the source article); context: Wikipedia, "Pugh's closing lemma", section "Formal statement" (revision oldid=1304222873, https://en.wikipedia.org/w/index.php?title=Pugh%27s_closing_lemma&oldid=1304222873), citing C. C. Pugh, "An Improved Closing Lemma and a General Density Theorem", Amer. J. Math. 89 (4) (1967), 1010-1021, https://doi.org/10.2307/2373414

import Mathlib
import Definitions.Def_PughClosingLemma_nonwandering

open scoped Topology

namespace PughClosingLemma

theorem nonwanderingSet_nonempty {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] (f : X → X) : (nonwanderingSet f).Nonempty := by sorry

end PughClosingLemma
