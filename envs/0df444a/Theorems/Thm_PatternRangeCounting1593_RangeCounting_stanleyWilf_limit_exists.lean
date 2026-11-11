-- Prove2me | Theorems.Thm_PatternRangeCounting1593_RangeCounting_stanleyWilf_limit_exists
-- name    : PatternRangeCounting1593.RangeCounting.stanleyWilf_limit_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:42.874642+00:00
-- url     : https://prove2.me/theorems/761ab4d5-8a45-40d3-9a7f-bfd2b319ca93
-- title:
--   Existence of the Stanley–Wilf limit for patterns of length at least three
-- statement:
--   Let $\pi$ be a permutation pattern of length $k\ge 3$. Then the limit
--   $$s_\pi=\lim_{n\to\infty}|\mathrm{Av}_n(\pi)|^{1/n}$$
--   exists, and $s_\pi\ge 1$.
--
--   The paper's space bound $2n\log s_\pi+o_\pi(n)$ refers to this limit; finiteness is the Stanley–Wilf conjecture proved by Marcus and Tardos, and existence of the limit follows from Arratia's supermultiplicativity argument.
--
--   Differences from the source:
--   - generalization: existence and finiteness of the Stanley–Wilf limit for the patterns used by the representation → the same limit assertion together with 1 ≤ s_π for |π| ≥ 3; reason: at least one of the increasing and decreasing permutations avoids such a pattern at every length; the extra inequality makes the logarithm convention explicit
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), §1.1, printed p. 1 (PDF p. 2), citing Arratia 1999 [Arr99] and Marcus–Tardos 2004 [MT04]; supporting theorem (not numbered in the paper)

import Mathlib
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Perm
set_option autoImplicit false
open Filter Topology

namespace PatternRangeCounting1593.RangeCounting

/-- For a pattern of length at least three, `|Av_n(π)|^{1/n}` converges to the Stanley–Wilf limit
`s_π`, and `s_π ≥ 1` (Arratia 1999; Marcus–Tardos 2004). -/
theorem stanleyWilf_limit_exists {k : ℕ} (π : Equiv.Perm (Fin k)) (hk : 3 ≤ k) :
    Tendsto (fun n : ℕ => ((Av n π).card : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 (swLimit π)) ∧
      1 ≤ swLimit π := by sorry

end PatternRangeCounting1593.RangeCounting
