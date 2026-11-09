-- Prove2me | Theorems.Thm_TwoMasterRoommates_Capped_optional_exchange
-- name    : TwoMasterRoommates.Capped.optional_exchange
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:43:47.400201+00:00
-- url     : https://prove2.me/theorems/09c00a4a-22a8-479f-a6a5-68be2cbc91f7
-- title:
--   §A.4 — optional-token prefix exchange
-- statement:
--   Let $K$ have active population $W$, mandatory tokens $T$, optional tokens $J$, and common marked set $U$. Order $J$ by its original rank with a fixed identity convention for ties, and let $P_\ell$ be its first $\ell$ identities, where $0\le\ell\le |J|$. Then
--
--   $$\exists\text{ stable completion using exactly }\ell\text{ optional tokens on actives}\quad\Longleftrightarrow\quad |J|-\ell\text{ is even and the kernel on }W\cup T\cup P_\ell\text{ has a mandatory completion}.$$
--
--   The restricted kernel is constructed on precisely that subpopulation and keeps all active caps and ranks. Unused optional tokens pair only in their inert complete clique. This exact equivalence retains both directions of the exchange reduction without adding eligibility or cost restrictions.
--
--   Differences from the source:
--   - generalization: real-valued weak ranks → ranks in any linear order; reason: finite attained values and their comparisons embed in the real source domain; specialize the rank type to the reals
--   - encoding: finite identity populations with arbitrary personal caps → finite labelled types, fixed-point-free involutions, and WithTop upper caps; reason: labels do not restrict populations; top is an infinite cap and every blocking comparison remains original and strict
--   - encoding: an integer optional-token count between zero and |J| → a natural number ℓ with ℓ ≤ |J| and the constructed subtype kernel; reason: the range condition prevents truncated subtraction from hiding an invalid count
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 12 (PDF p. 13), §A.4 optional-token exchange and equivalence

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Kernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped

/-- §A.4: prefix exchange and the exact mandatory-subproblem characterization. -/
theorem optional_exchange {ι R : Type} [Fintype ι] [LinearOrder ι] [LinearOrder R]
    (K : Kernel ι R) (l : ℕ)
    (hl : l ≤ Fintype.card {v // K.kind v = .optional}) :
    (∃ M, KSolution K M ∧
      Fintype.card {v // K.kind v = .optional ∧ K.kind (M v) = .active} = l) ↔
    Even (Fintype.card {v // K.kind v = .optional} - l) ∧
      ∃ M, KSolution (prefixKernel K l) M := by sorry

end TwoMasterRoommates.Capped
