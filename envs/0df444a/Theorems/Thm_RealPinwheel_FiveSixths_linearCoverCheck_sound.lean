-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_linearCoverCheck_sound
-- name    : RealPinwheel.FiveSixths.linearCoverCheck_sound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:22:24.330193+00:00
-- url     : https://prove2.me/theorems/73af0433-03e0-45bf-8a13-00b99f16cd7f
-- title:
--   Soundness of exact linear coverage certificates
-- statement:
--   Let $d_1\ge\cdots\ge d_n>0$ be real densities, and let $k$ be the number of initial coordinates whose sum is bounded by $5/6$. Suppose a finite linear coverage tree passes its exact integer checks for an indexed family of $N$ annotated boxes. Then
--
--   $$\sum_{i=1}^{k}d_i\le5/6\quad\Longrightarrow\quad\exists j<N:\ d\in B_j.$$
--
--   The initial sum is interpreted over available task positions. Taking $k=n$ gives the density domain, and taking $k=n-1$ gives the potential domain. The conclusion concerns the rational annotations; a separate witness theorem proves that each annotated box yields a valid periodic schedule. No rationality assumption is made on the density vector.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (3), Section 4 queries (4)–(5), printed pp. 9–10 (PDF pp. 10–11), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf; explicit linear-combination verification of those real-arithmetic domain inclusions.

import Definitions.Def_RealPinwheel_FiveSixths_LinearCertificate
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.linearCoverCheck_sound {n : ℕ} (k : ℕ) (N : ℕ) (codes : ℕ → CycleCode) (tree : LinearCoverTree n)
    (hc : linearCoverCheck N codes (initialAtoms n k) tree = true)
    (d : Fin n → ℝ) (hpos : ∀ i, 0 < d i) (hord : Antitone d)
    (hsum : (∑ i, if i.val < k then d i else 0) ≤ (5 : ℝ) / 6) :
    ∃ j : Fin N, codeBox (codes j.val) d := by sorry
