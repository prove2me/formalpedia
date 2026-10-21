-- Prove2me | Theorems.Thm_VolDisclosure_Evidence_proposition_2
-- name    : VolDisclosure.Evidence.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:05.467991+00:00
-- url     : https://prove2.me/theorems/6353765b-be9a-40c3-9f3c-d3d6db9a67e3
-- title:
--   Proposition 2, (4), p. 16 — the cash payout boundary inf{v : s(v) = s*} equals v̄ = r⁻¹(1+r)pδ
-- statement:
--   Fix parameters satisfying the standing assumptions of §3, an evidence probability $\pi \in [0,1)$, and let $s$ be a firm value (fixed point of (T)). The cash payout boundary of $s$, the smallest promised utility at which firm value reaches its first best (definition (3), p. 16), is
--   $$
--   \inf\{v \ge 0 : s(v) = s^*\} = \bar v = r^{-1}(1+r)p\delta .
--   $$
--   In particular the boundary does not depend on the availability of evidence $\pi$.
--
--   **Formalization Note.** Only the $s$-half of definition (3) is formalized; the half involving the value $f$ of the problem with an investment option, (F), and the cash compensation formula (5) are not part of this statement.
-- source:
--   Fu & Trigilia, Voluntary Disclosure, Moral Hazard and Default Risk, working paper (August 28, 2019), p. 16, Proposition 2, (3), (4); proof p. 38

import Mathlib
import Definitions.Def_VolDisclosure_Evidence_Model

namespace VolDisclosure.Evidence

/-- Proposition 2, (4) (p. 16; proof p. 38): the cash payout boundary
`inf {v : s(v) = s*}` equals `v̄ = r⁻¹(1+r)pδ`. -/
theorem proposition_2 (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π < 1)
    (s : ℝ → ℝ) (hs : IsValue P π s) :
    sInf {v : ℝ | 0 ≤ v ∧ s v = P.sStar} = P.vBar := by sorry

end VolDisclosure.Evidence
