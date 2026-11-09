-- Prove2me | Theorems.Thm_TwoMasterRoommates_Capped_cap_compression
-- name    : TwoMasterRoommates.Capped.cap_compression
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:39:03.776736+00:00
-- url     : https://prove2.me/theorems/5c69660d-415e-4784-b1ae-698b10d289f9
-- title:
--   §B — dense-rank compression preserves capped solutions
-- statement:
--   Let $I$ be a two-master instance, and compress each whole rank map by replacing a rank with the number of distinct attained values below it. Keep observer classes, send an infinite cap to infinity, and send a finite cap to the number of attained values in that observer's own master below or equal to the cap, minus one in the integers. Then all strict master comparisons and all candidate cap acceptances are preserved, both compressed maps have dense ranges, and
--
--   $$\operatorname{IsSolution}(I,M)\quad\Longleftrightarrow\quad\operatorname{IsSolution}(I.\mathrm{compress},M)\qquad\text{for every }M.$$
--
--   The range of a compressed map with $s$ attained values is exactly $\{0,\ldots,s-1\}$. This includes the empty range and caps below every rank. This preserves the full set of feasible stable matchings rather than only the existence answer.
--
--   Differences from the source:
--   - generalization: real-valued weak ranks → ranks in any linear order; reason: finite attained values and their comparisons embed in the real source domain; specialize the rank type to the reals
--   - encoding: finite identity populations with arbitrary personal caps → finite labelled types, fixed-point-free involutions, and WithTop upper caps; reason: labels do not restrict populations; top is an infinite cap and every blocking comparison remains original and strict
--   - encoding: tier indices and empty-prefix cut −1 → integer tier indices with integer subtraction in the cap formula; reason: no natural subtraction is truncated; whole master values include self entries
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 4 (PDF p. 5), §3 cap conversion; p. 12 (PDF p. 13), Appendix B cap compression

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Compression

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped

/-- §3 and Appendix B: whole-rank compression, with the observer's own cap conversion. -/
theorem cap_compression {R : Type} [LinearOrder R] {n : ℕ} (I : Instance R n) :
    SameComparisons I I.compress ∧ Dense I.compress ∧
      ∀ M, IsSolution I M ↔ IsSolution I.compress M := by sorry

end TwoMasterRoommates.Capped
