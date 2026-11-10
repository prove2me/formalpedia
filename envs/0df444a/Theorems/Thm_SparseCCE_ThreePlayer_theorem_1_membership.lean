-- Prove2me | Theorems.Thm_SparseCCE_ThreePlayer_theorem_1_membership
-- name    : SparseCCE.ThreePlayer.theorem_1_membership
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:06:04.127775+00:00
-- url     : https://prove2.me/theorems/62e4f947-c0e6-4a5c-8571-a6ea644a6a1c
-- title:
--   Proof of Theorem 1, membership — $T$-sparse $1/p(N)$-CCE of three-player games is in PPAD
-- statement:
--   For every $T\ge1$ and every polynomial $p$ with $p(N)\ge1$, the search problem `SparseCCE3 T p` — computing a rational $1/p(N)$-approximate $T$-sparse CCE of a three-player normal-form game with rational utilities in $[0,1]$ — is in PPAD (total, and reducible to End-of-Line). The source's argument: it suffices to compute a rational approximate Nash equilibrium at the required inverse-polynomial accuracy [DGP09, §3.2], a product distribution being $T$-sparse for every $T\ge1$.
--
--   Differences from the source:
--   - generalization: membership in PPAD of the problem of Theorem 1 for the polynomial chosen there → SparseCCE3 T p ∈ QuasiStrictNE.PPAD for every T ≥ 1 and every polynomial p with p ≥ 1; reason: The proof gives membership at every inverse-polynomial accuracy and for every fixed T ≥ 1, so it includes the polynomial selected for hardness
--   - encoding: PPAD membership → membership in QuasiStrictNE.PPAD; reason: The reused class requires totality and a polynomial-time search reduction to End-of-Line, without a bound on all answer lengths
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). Proof of Theorem 1, p. 19, citing [DGP09, Section 3.2].

import Mathlib
import Definitions.Def_QuasiStrictNE_PPAD
import Definitions.Def_SparseCCE_ThreePlayer_SparseCCE3

namespace SparseCCE.ThreePlayer

/-- **Proof of Theorem 1, membership** (p. 19, citing [DGP09, §3.2]): for every `T ≥ 1` and every
polynomial `p ≥ 1`, computing a `1/p(N)`-approximate `T`-sparse CCE of a three-player game is in
PPAD — it suffices to compute a rational approximate Nash equilibrium (a product distribution,
which is `T`-sparse for every `T ≥ 1`) at the required inverse-polynomial accuracy. -/
theorem theorem_1_membership (T : ℕ) (hT : 1 ≤ T) (p : Polynomial ℕ) (hp : ∀ n, 1 ≤ p.eval n) :
    SparseCCE3 T p ∈ QuasiStrictNE.PPAD := by sorry

end SparseCCE.ThreePlayer
