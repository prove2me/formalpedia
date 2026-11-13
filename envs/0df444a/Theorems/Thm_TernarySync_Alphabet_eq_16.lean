-- Prove2me | Theorems.Thm_TernarySync_Alphabet_eq_16
-- name    : TernarySync.Alphabet.eq_16
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-11T03:54:44.105202+00:00
-- url     : https://prove2.me/theorems/b97212b0-abd1-453a-97d8-ea8c1fe3a098
-- title:
--   Eq. (16) — neighbour-weight tail: $\sum_{F \sim E_{t,\ell}} x(F) \le 3\sum_{r \ge L}(\ell + r)e^{-r/80} < \ell/490$
-- statement:
--   For an outer word of length $N$, consider the long bad events $E_{u,r}$ (integer $r > L = 1000$, available start $u$) of Section 4, where $E_{u,r}$ depends on the macroblock choices whose blocks meet $[u, u+2r)$, and two different events are neighbours when they share such a choice. With the local-lemma weights $x(E_{u,r}) = e^{-r/80}$ of Equation (15), every long bad event $E_{t,\ell}$ satisfies
--
--   $$\sum_{F \sim E_{t,\ell}} x(F) \le 3 \sum_{r \ge L} (\ell + r)\, e^{-r/80} < \frac{\ell}{490}. \tag{16}$$
--
--   The first inequality counts at most $2\ell + 2r + 37 \le 3(\ell + r)$ neighbours of each length $r$; the second is a geometric-tail estimate. Together with (14) this verifies the local-lemma criterion (5).
--
--   **Formalization Note.** Events are indexed by pairs $(u, r)$ (`availEvents N`: $r > 1000$, $u + 2r \le 18N$, 0-based); `neighbours N t ℓ` is the set of the other pairs sharing a macroblock choice with $(t,\ell)$. The series $\sum_{r \ge 1000}$ is written as $\sum_{r' \ge 0}$ with $r = r' + 1000$ (`tsum`; the series converges).
--
--   Differences from the source:
--   - encoding: 1-based half-open factors $S[i,j)$ with $1 \le i \le j \le n+1$ → 0-based `factor S i j` = positions $i,\dots,j-1$, so the ranges shift by one (e.g. $k \le n+1$ becomes $k \le n$); reason: index shift only; the same factors and the same instances
--   - encoding: the event family of a fixed outer word T of length N → the events indexed by pairs (t, ℓ) for a length N, without T; reason: the events' variables and neighbours depend on T only through N = |T|
--   - encoding: the series Σ_{r ≥ L} → ∑' r' : ℕ with r = r' + 1000; reason: reindexing of a convergent series of nonnegative terms
-- source:
--   Xu, Fu, Qiao, Tao, Synchronization Strings over a Ternary Alphabet, STOC 2027 submission (manuscript sha256 1b74ae6d…), p. 17 (PDF 18), §4, Eqs. (15)–(16)

import Mathlib
import Definitions.Def_TernarySync_Alphabet_RandomSource

set_option autoImplicit false

namespace TernarySync.Alphabet

/-- Equation (16) (p. 17): with the local-lemma weights `x(E_{u,r}) = e^{−r/80}` of
Equation (15), for every long bad event `E_{t,ℓ}` of an outer word of length `N`, the weights of
its neighbours (the other long bad events sharing a macroblock choice with it) satisfy
`∑_{F ∼ E_{t,ℓ}} x(F) ≤ 3 ∑_{r ≥ L} (ℓ + r) e^{−r/80} < ℓ/490`, `L = 1000`; the series is
written with `r = 1000 + r'`, `r' ≥ 0`. -/
theorem eq_16 (N t ℓ : ℕ) (hE : (t, ℓ) ∈ availEvents N) :
    ∑ p ∈ neighbours N t ℓ, Real.exp (-(p.2 : ℝ) / 80) ≤
        3 * ∑' r : ℕ, ((ℓ : ℝ) + ((r : ℝ) + 1000)) * Real.exp (-((r : ℝ) + 1000) / 80) ∧
      3 * ∑' r : ℕ, ((ℓ : ℝ) + ((r : ℝ) + 1000)) * Real.exp (-((r : ℝ) + 1000) / 80) <
        (ℓ : ℝ) / 490 := by sorry

end TernarySync.Alphabet
