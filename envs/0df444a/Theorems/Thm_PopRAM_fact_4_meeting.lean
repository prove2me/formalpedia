-- Prove2me | Theorems.Thm_PopRAM_fact_4_meeting
-- name    : PopRAM.fact_4_meeting
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:25:38.42948+00:00
-- url     : https://prove2.me/theorems/cd1aba8c-e30c-4dbf-b33d-4328f6ec8fdf
-- title:
--   §C.2, before Fact 4 — two given agents meet with probability 1, after expected exactly $n(n-1)/2$ interactions
-- statement:
--   For $n\ge2$ agents and two distinct agents $a,b$, under the uniform random scheduler $a$ and $b$ interact (in either orientation) with probability $1$, and the expected number of interactions up to and including their first interaction is exactly
--   $$\frac{n(n-1)}{2},$$
--   i.e. expected time $(n-1)/2=O(n)$.
--
--   This is the waiting time of the backup subroutines GET$^b$ and PUT$^b$, in which the leader waits for the agent holding the requested bit; Fact 4 multiplies it by the $O(w)$ calls of an instruction.
--
--   Differences from the source:
--   - generalization: with probability 1, in expected time O(n) → with probability 1, expected exactly n(n − 1)/2 interactions; reason: the exact value implies the O(n) bound
--   - encoding: the leader waiting for the agent holding the specified bit → two fixed distinct agents on the bare scheduler; reason: the meeting time of two agents does not depend on the protocol's states
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), §C.2, p.33 (PDF p.34), the two sentences before Fact 4

import Mathlib
import Definitions.Def_PopRAM_Meeting

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace PopRAM

/-- **Fact 4, meeting time** (Gąsieniec, Grodzicki, Stachowiak, arXiv:2611.06178, held version
sha256 f13223b3…, §C.2, p.33, PDF p.34, the two sentences before Fact 4). "Each of these
subroutines completes once the leader interacts with the agent holding the specified bit. Such an
interaction occurs with probability 1, in expected time O(n)."

For `n ≥ 2` agents and two distinct agents `a, b`, under the uniform random scheduler the two agents
interact (in either orientation) with probability `1`, and the expected number of interactions up to
and including their first interaction is exactly `n(n − 1)/2`, i.e. expected time `(n − 1)/2 = O(n)`.

**Formalization Note** The exact value is stated in place of `O(n)`. -/
theorem fact_4_meeting (n : ℕ) (hn : 2 ≤ n) (a b : Fin n) (hab : a ≠ b) :
    sched n {ω | meetTime a b ω = ⊤} = 0 ∧
    ∫⁻ ω, (meetTime a b ω : ℝ≥0∞) ∂(sched n) = ((n * (n - 1) : ℕ) : ℝ≥0∞) / 2 := by sorry

end PopRAM
