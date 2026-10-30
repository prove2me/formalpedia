-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_rank_tester_adjacent_uniform
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.rank_tester_adjacent_uniform
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:19:40.075625+00:00
-- url     : https://prove2.me/theorems/457856d1-9ea5-41bc-8cc3-a293e727f78c
-- title:
--   Proposition 6.4
-- statement:
--   For every $r\ge1$ and $d\ge r+1$, the Rank Tester distinguishes uniform spectra of ranks $r$ and $r+1$ with
--
--   $$n=O(r^2)$$
--
--   copies, using an absolute constant independent of $d$ and the eigenbasis. It accepts the rank-$r$ case with certainty and rejects the rank-$(r+1)$ case with probability at least $2/3$. This is a one-sided alternative for adjacent uniform ranks.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 58, Proposition 6.4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Proposition 6.4, arXiv:1501.05028v1, PDF p.58. State the headline absolute O bound; no need to import the proof’s nonsharp proposed constant 6 at small r. -/
theorem rank_tester_adjacent_uniform
    : ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 1 ≤ r →
      ∀ d : ℕ, r+1 ≤ d → ∃ n : ℕ, (n : ℝ) ≤ C*r^2 ∧
        ∀ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho →
          (UniformRank r rho → rankAccept n r rho = 1) ∧
          (UniformRank (r+1) rho → rankAccept n r rho ≤ 1/3) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
