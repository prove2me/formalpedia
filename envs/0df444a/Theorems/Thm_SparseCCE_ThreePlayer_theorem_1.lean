-- Prove2me | Theorems.Thm_SparseCCE_ThreePlayer_theorem_1
-- name    : SparseCCE.ThreePlayer.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:06:05.097849+00:00
-- url     : https://prove2.me/theorems/b0810507-faef-47a7-8898-f3b0c87e36df
-- title:
--   Theorem 1 — for every fixed $T\ge1$, inverse-polynomially approximate $T$-sparse CCE of three-player games is PPAD-complete
-- statement:
--   For every integer $T\ge1$ there is a polynomial $p$ with natural coefficients and $p(N)\ge1$ for all $N$ such that the search problem `SparseCCE3 T p` is PPAD-complete: it lies in PPAD, and every PPAD problem reduces to it by a polynomial-time search reduction. `SparseCCE3 T p` asks, given a three-player normal-form game with rational utilities in $[0,1]$ (encoding length $N$), for rational weights $w\in\Delta([T])$ and rational mixed strategies $p^{(t)}_j$ such that $\sum_tw_t\bigotimes_jp^{(t)}_j$ is a $1/p(N)$-approximate coarse correlated equilibrium.
--
--   The proof is on p. 19; it uses Lemma A.3 (p. 32, size of the reduction and accuracy $\varepsilon/(2R_{\max})\ge\varepsilon_0/(9344M^{12})$), which is not a milestone of this mission.
--
--   Differences from the source:
--   - reading: "inverse-polynomially approximate": ε = 1/p(N) for some polynomial p that may depend on T (p. 13) → ∀ T ≥ 1, ∃ p : Polynomial ℕ with p(n) ≥ 1 for all n, PPADComplete (SparseCCE3 T p); reason: the source’s definition; ∀ p would be false (p ≡ 2 asks for a 1/2-CCE)
--   - encoding: a three-player normal-form game of encoding length N; the answer represented by weights and components → gameCode (action counts and rational utility tables in canonical order); sparseCode (rational weights and components); N = length of the instance string; answers of any length; reason: a concrete binary code; the source allows weights and components
--   - encoding: CCEGap_j(µ) = max over D_j ∈ Δ(B_j) → IsEpsCCE: every mixed deviation D_j gains at most ε; reason: the maximum is attained, so the two conditions coincide
--   - encoding: PPAD-complete → QuasiStrictNE.PPADComplete (membership in QuasiStrictNE.PPAD and every PPAD problem reduces by CardinalMatching.SearchReduces); reason: the published platform definitions; no answer-length bound
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). Theorem 1, p. 5; proof p. 19.

import Mathlib
import Definitions.Def_QuasiStrictNE_PPADComplete
import Definitions.Def_SparseCCE_ThreePlayer_SparseCCE3

namespace SparseCCE.ThreePlayer

/-- **Theorem 1**, p. 5 (proof p. 19): for every fixed integer `T ≥ 1`, computing an
inverse-polynomially approximate `T`-sparse coarse correlated equilibrium of a three-player
normal-form game is PPAD-complete: there is a polynomial `p` with `p(N) ≥ 1` such that the search
problem `SparseCCE3 T p` (accuracy `1/p(N)`) is in PPAD and PPAD-hard. -/
theorem theorem_1 :
    ∀ T : ℕ, 1 ≤ T → ∃ p : Polynomial ℕ, (∀ n, 1 ≤ p.eval n) ∧
      QuasiStrictNE.PPADComplete (SparseCCE3 T p) := by sorry

end SparseCCE.ThreePlayer
