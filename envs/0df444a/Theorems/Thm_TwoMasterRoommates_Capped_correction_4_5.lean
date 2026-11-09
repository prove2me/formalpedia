-- Prove2me | Theorems.Thm_TwoMasterRoommates_Capped_correction_4_5
-- name    : TwoMasterRoommates.Capped.correction_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:51:32.660365+00:00
-- url     : https://prove2.me/theorems/6cf7835d-a06f-46cf-ab5e-747802835358
-- title:
--   Eqs. (4)–(5) — locality of the exact Hall correction
-- statement:
--   Let $K$ be a finite common-order kernel and $e=(u,v)$ a permitted positive edge with $\alpha=r(u)<\beta=r(v)$. Thus the source is active and its cap is at least $\beta$; the partner is either active with cap at least $\alpha$, or a mandatory token with marked source. Let $\epsilon_e$ be one for an active partner and zero otherwise. Define $\Delta_e(t)$ by equation (4), including the sum over all strict interior actives and the convention $d_0(s)=r(s)$ on tokens. Then both locality identities hold:
--
--   $$\Delta_e(t)=0\quad(t<\alpha),\qquad\Delta_e(t)=2\epsilon_e\quad(t\ge\beta).$$
--
--   The correction is integer-valued, so supply and job deletions use ordinary signed subtraction. These identities describe the complete exterior behavior of the exact correction, including cap values below the first attained rank.
--
--   Differences from the source:
--   - generalization: real-valued weak ranks → ranks in any linear order; reason: finite attained values and their comparisons embed in the real source domain; specialize the rank type to the reals
--   - generalization: the surrounding kernel has only mandatory tokens → additional optional tokens are allowed elsewhere in the kernel, while the selected positive edge remains active–active or marked–mandatory; reason: the formula uses only actives and its selected endpoint; specialize to a mandatory kernel
--   - encoding: indicator sums and possibly infinite caps → integer indicator sums and WithTop caps with finite minima; reason: no infinity is subtracted; the token extension is a definition
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 10 (PDF p. 11), equations (4)–(5)

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Residual

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped

/-- Equations (4)–(5); correction is defined by (4), including the printed token convention. -/
theorem correction_4_5 {ι R : Type} [Fintype ι] [DecidableEq ι] [LinearOrder R]
    (K : Kernel ι R) (e : ι × ι) (he : PositiveEdge K e) :
    (∀ t, t < K.r e.1 → correction K e t = 0) ∧
    (∀ t, K.r e.2 ≤ t → correction K e t =
      2 * (if K.kind e.2 = .active then 1 else 0)) := by sorry

end TwoMasterRoommates.Capped
