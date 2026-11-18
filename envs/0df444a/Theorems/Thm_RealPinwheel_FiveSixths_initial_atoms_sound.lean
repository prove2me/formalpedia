-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_initial_atoms_sound
-- name    : RealPinwheel.FiveSixths.initial_atoms_sound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:48:01.834439+00:00
-- url     : https://prove2.me/theorems/f7373b1b-f447-4067-903b-3e3cf1ae04a3
-- title:
--   initial atoms sound
-- statement:
--   For a positive antitone real vector $d$ satisfying the initial-coordinate sum bound, all inequalities in the coverage checker's initial context hold:
--
--   $$d_i>0,\quad d_{i+1}\le d_i,\quad\sum_{i<k}d_i\le5/6\quad\Longrightarrow\quad d\in R_{\mathrm{initial}(n,k)}.$$
--
--   The choices $k=n$ and $k=n-1$ represent the density and potential domains respectively.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Exact real-domain coverage interface.

import Definitions.Def_RealPinwheel_FiveSixths_LinearCertificate
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.initial_atoms_sound {n k : ℕ} (d : Fin n → ℝ)
    (hpos : ∀ i, 0 < d i) (hord : Antitone d)
    (hsum : (∑ i, if i.val < k then d i else 0) ≤ (5 : ℝ) / 6) :
    ∀ a ∈ initialAtoms n k, a.Holds d  := by sorry
