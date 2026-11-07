-- Prove2me | Theorems.Thm_ReadTwiceCount_theorem_6_2
-- name    : ReadTwiceCount.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:44:14.785209+00:00
-- url     : https://prove2.me/theorems/018608c1-032f-4f9e-a457-95cce695e3f9
-- title:
--   Theorem 6.2 — every run of the marginal procedure satisfies (11)
-- statement:
--   **Theorem 6.2.** The marginal procedure satisfies (11) on every positive dangling state: for a global clause bound $n\ge1$, a read-twice normalized state $H$ with $s\le n$ clauses, a positive dangling query $h$ and a density $a>0$, every run of $\mathrm{Solve}(H,h,a)$ returns a rational $U$ with
--   $$1\le y(H,h)\le U\le s+1,\qquad U-y(H,h)\le a(s+1).$$
--
--   This is the accuracy guarantee of the marginal procedure; the counting reduction of §8 applies it to each private-literal query.
--
--   Differences from the source:
--   - generalization: the marginal procedure (a fixed expansion order and dyadic $r_i$) → every run of the procedure: any positive block meeting the stopping rule and any rational $r_i\in[\sqrt{D_i},q\sqrt{D_i}]$; reason: the paper's procedure produces one of these runs, and its proof (Lemma 6.1, (27)–(29)) uses only these properties
--   - reading: "on every positive dangling state" with a global $n$ → hypotheses $n\ge1$, $s\le n$, $a>0$, read-twice normalized positive dangling $(H,h)$; reason: the standing context of §3 (p.4) and §5 (p.6: "The parameter $a>0$ is the accuracy density")
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), Theorem 6.2, p.10; display (11), p.6

import Mathlib
import Definitions.Def_ReadTwiceCount_SolveRun

namespace ReadTwiceCount

/-- **Theorem 6.2** (He, *A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments*, STOC 2027
submission (manuscript sha256 7a2a9dcd…), Theorem 6.2, p.10): "The marginal
procedure satisfies (11) on every positive dangling state", where (11) (§5, p.6) reads: on an
s-clause state, it returns a rational upper bound U satisfying
1 ≤ y(H, h) ≤ U ≤ s + 1, U − y(H, h) ≤ a(s + 1).

Every run `R` of `Solve(H, h, a)` with global clause bound `n ≥ 1`, on a positive dangling query of a
read-twice normalized state with `s ≤ n` clauses and density `a > 0`, returns a `U` satisfying every
clause of (11).

**Formalization Note** `SolveRun` covers every run of the procedure (any expansion order, any
rational `rᵢ ∈ [√Dᵢ, q√Dᵢ]`), so the theorem covers the paper's deterministic procedure. -/
theorem theorem_6_2 (n : ℕ) (hn : 1 ≤ n) {M : ℕ} (H : Formula M) (h : Lit M) (a U : ℚ)
    (R : SolveRun n H h a U) (ha : 0 < a) (hRT : ReadTwice H) (hN : Normalized H)
    (hD : IsDangling H h) (hP : IsPositive H h) (hs : H.clauses.length ≤ n) :
    1 ≤ yCoord H h ∧ yCoord H h ≤ U ∧ U ≤ (H.clauses.length : ℚ) + 1 ∧
      U - yCoord H h ≤ a * ((H.clauses.length : ℚ) + 1) := by sorry

end ReadTwiceCount
