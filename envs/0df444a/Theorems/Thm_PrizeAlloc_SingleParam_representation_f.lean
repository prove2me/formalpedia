-- Prove2me | Theorems.Thm_PrizeAlloc_SingleParam_representation_f
-- name    : PrizeAlloc.SingleParam.representation_f
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:21.946201+00:00
-- url     : https://prove2.me/theorems/b557ff22-4c17-48d6-bb3d-dd55d269f7d0
-- title:
--   p. 31 — the two-competitor allocation path of the rule is the graph of a representation f
-- statement:
--   Let $\varphi$ be a prize allocation rule satisfying order preservation, winner strict endowment monotonicity and endowment continuity. Let $u\ne v$ be two competitors and let $\mathcal R$ be the two-competitor ranking in which $u$ is first and $v$ second. Then there is a continuous, non-decreasing $f:\mathbb R_+\to\mathbb R_+$ with $f(x)\le x$ such that:
--
--   1. for each $x\ge 0$,
--   $$\varphi_u(\{u,v\},\mathcal R,x+f(x))=x,\qquad \varphi_v(\{u,v\},\mathcal R,x+f(x))=f(x);$$
--   2. $f$ is well defined: if $x,y\ge 0$, $\varphi_u(\{u,v\},\mathcal R,x+y)=x$ and $\varphi_v(\{u,v\},\mathcal R,x+y)=y$, then $y=f(x)$.
--
--   In the proof of Theorem 2 this $f$ is the representation of the rule.
--
--   **Formalization Note** Endowment continuity is a hypothesis here; in the paper it follows from endowment monotonicity by Lemma 1 (p. 10), which belongs to the companion mission on interval rules. Anonymity is not needed for this step. The standing assumption that $U$ is countable with at least three elements is omitted (only two competitors are used).
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, p. 31, proof of Theorem 2, definition of f

import Mathlib
import Definitions.Def_PrizeAlloc_SingleParam_Setting
import Definitions.Def_PrizeAlloc_SingleParam_Rules

namespace PrizeAlloc.SingleParam

theorem representation_f {U : Type*} [DecidableEq U]
    (φ : List U → ℝ → U → ℝ) (hφ : PrizeAlloc.Interval.IsPrizeRule φ) (hOP : PrizeAlloc.Interval.OrderPreserving φ)
    (hW : PrizeAlloc.Interval.WinnerStrictMonotone φ) (hC : PrizeAlloc.Interval.EndowmentContinuous φ) (u v : U) (huv : u ≠ v) :
    ∃ f : ℝ → ℝ, IsRepresentation f ∧
      (∀ x, 0 ≤ x → φ [u, v] (x + f x) u = x ∧ φ [u, v] (x + f x) v = f x) ∧
      (∀ x y, 0 ≤ x → 0 ≤ y → φ [u, v] (x + y) u = x → φ [u, v] (x + y) v = y → y = f x) := by sorry

end PrizeAlloc.SingleParam
