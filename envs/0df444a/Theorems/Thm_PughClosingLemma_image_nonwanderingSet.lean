-- Prove2me | Theorems.Thm_PughClosingLemma_image_nonwanderingSet
-- name    : PughClosingLemma.image_nonwanderingSet
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T21:23:40.98364+00:00
-- url     : https://prove2.me/theorems/1d612d39-0d7b-4fcf-9bdc-b668becee289
-- title:
--   The nonwandering set of a homeomorphism is invariant: $f(\Omega(f))=\Omega(f)$
-- statement:
--   Let $X$ be a topological space and $f\colon X\to X$ a homeomorphism. Then the nonwandering set is invariant under $f$:
--
--   $$f(\Omega(f))=\Omega(f).$$
--
--   Invariance makes $\Omega(f)$ a closed invariant set carrying the recurrent dynamics of $f$, the set on which the closing lemma operates.
-- source:
--   Standard property of the nonwandering set (not stated separately in the source article); context: Wikipedia, "Pugh's closing lemma", section "Formal statement" (revision oldid=1304222873, https://en.wikipedia.org/w/index.php?title=Pugh%27s_closing_lemma&oldid=1304222873), citing C. C. Pugh, "An Improved Closing Lemma and a General Density Theorem", Amer. J. Math. 89 (4) (1967), 1010-1021, https://doi.org/10.2307/2373414

import Mathlib
import Definitions.Def_PughClosingLemma_nonwandering

open scoped Topology

namespace PughClosingLemma

theorem image_nonwanderingSet {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) :
    f '' nonwanderingSet f = nonwanderingSet f := by sorry

end PughClosingLemma
