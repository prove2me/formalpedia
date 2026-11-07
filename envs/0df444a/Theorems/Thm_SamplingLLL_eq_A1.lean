-- Prove2me | Theorems.Thm_SamplingLLL_eq_A1
-- name    : SamplingLLL.eq_A1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:00:47.673538+00:00
-- url     : https://prove2.me/theorems/d8a254b7-5d71-4a0f-96a1-204f824264b2
-- title:
--   (A1), pp.66–67 — joint violation bound of accepted sets
-- statement:
--   Let $Y$ be a set accepted by the search, $q$ the number of components of $H[Y]$, $p_a\ge\lambda(\mathrm{Bad}_a)$, and (C) hold on $G$. Then
--   $$
--   \lambda\Big(\bigcap_{b\in Y}\mathrm{Bad}_b\Big)\le2^{-q}\prod_{b\in Y}2p_b\le\frac12\prod_{b\in Y}2p_b. \tag{A1}
--   $$
--
--   Differences from the source: none.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), eq. (A1), pp.66–67

import Mathlib
import Definitions.Def_SamplingLLL_sllAnalysis

set_option autoImplicit false

namespace SamplingLLL

/-- (A1), pp.66–67: `λ(⋂_{b∈Y} Bad_b) ≤ 2^{-q} ∏_{b∈Y} 2p_b ≤ ½ ∏_{b∈Y} 2p_b`, with `q` the number of
components of `H[Y]`, for a set `Y` accepted by the search, assuming `p_a ≥ λ(Bad_a)` and (C) on `G`.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), eq. (A1), pp.66–67. -/
theorem eq_A1 {n m : ℕ} (I : AtomicCSP n m) (G S : Finset (Fin m)) (c : Fin m) (t : Leaf m)
    (ht : I.SearchNode G S c t) (p : Fin m → ℝ) (hp : ∀ a, ((I.badProb a : ℚ) : ℝ) ≤ p a)
    (hG : ∀ a ∈ G, I.SamplingGood p a) :
    ((I.jointBad t.1 : ℚ) : ℝ) ≤
        (1 / 2 : ℝ) ^ Nat.card (I.H.induce (t.1 : Set (Fin m))).ConnectedComponent *
          ∏ b ∈ t.1, (2 * p b) ∧
    (1 / 2 : ℝ) ^ Nat.card (I.H.induce (t.1 : Set (Fin m))).ConnectedComponent *
        ∏ b ∈ t.1, (2 * p b) ≤ 1 / 2 * ∏ b ∈ t.1, (2 * p b) := by sorry

end SamplingLLL
