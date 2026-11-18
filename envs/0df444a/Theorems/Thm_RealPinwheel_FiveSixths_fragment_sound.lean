-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_fragment_sound
-- name    : RealPinwheel.FiveSixths.fragment_sound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:45:46.075827+00:00
-- url     : https://prove2.me/theorems/007279ee-5aac-4189-b204-44c4405ad227
-- title:
--   fragment sound
-- statement:
--   Let $R_\Gamma$ be the real vectors satisfying a finite context of strict or non-strict integer linear inequalities, and let $B_0,\ldots,B_{N-1}$ be annotated boxes. If every arithmetic leaf and every child coverage obligation of a finite proof fragment is established, then
--
--   $$R_\Gamma\subseteq\bigcup_{j<N} B_j.$$
--
--   This is a modular soundness theorem: child coverage lemmas replace full child certificate data, while the conclusion still concerns arbitrary real vectors.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Exact real-domain coverage interface.

import Definitions.Def_RealPinwheel_FiveSixths_LinearFragment
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.fragment_sound {n : ℕ} (N : ℕ) (codes : ℕ → CycleCode)
    (Γ : List (LinearAtom n)) (tree : LinearFragment n)
    (hc : fragmentObligations N codes Γ tree)
    (d : Fin n → ℝ) (hΓ : ∀ a ∈ Γ, a.Holds d) :
    ∃ j : Fin N, codeBox (codes j.val) d  := by sorry
