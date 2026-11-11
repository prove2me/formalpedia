-- Prove2me | Theorems.Thm_PowerMinUncut_Threshold_theorem_11
-- name    : PowerMinUncut.Threshold.theorem_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:44:54.543197+00:00
-- url     : https://prove2.me/theorems/397bf27a-3023-4bcf-a977-0bb75917c8c9
-- title:
--   Theorem 11 — bounded-bit rounding: a randomized Turing machine outputs r_i/√(r_i·r_i) of cost ≤ (C + ζ)OPT w.p. ≥ 1 − ω, deterministic polynomial resources
-- statement:
--   Fix integers $q\ge2$ and $k>q$. There is one randomized Turing-machine algorithm (constants $c,d$ depending only on $k,q$) such that for every finite loopless graph $G$ on $N$ vertices with nonnegative rational weights of total one, and all rationals $\zeta>0$ and $0<\omega<1$ given in binary, it returns exactly feasible vectors
--   $$v_i=\frac{r_i}{\sqrt{r_i\cdot r_i}},\qquad r_i\in\mathbb Q^k\setminus\{0\},$$
--   such that with probability at least $1-\omega$
--   $$\sum_{ij\in E}w_{ij}\|v_i+v_j\|^q\le (C_{k,q}+\zeta)\,\mathrm{OPT}_{k,q}(G).$$
--   Its running time, random-bit budget and output-description length are at most $c(1+\ell+N+|E|+\max\{1,1/\zeta\}+1+\log(1/\omega))^d$ on every random string ($\ell$ the binary input length, which includes $\zeta,\omega$). Square roots are positive.
--
--   Differences from the source:
--   - encoding: randomized Turing-machine algorithm; probability; random-bit budget → one Cook machine over a finite alphabet Γ ⊇ Sym reading the input and a coin string of length T = resBound; probability = fraction of the 2^T coin strings; reason: standard coin-string model; reading at most T coins is the random-bit budget
--   - encoding: polynomial in ℓ, N, |E|, max{1, 1/ζ}, 1 + log(1/ω) for fixed k, q → ⌊c·(1 + ℓ + N + |E| + max(1, 1/ζ) + (1 + log(1/ω)))^d⌋ with c, d chosen before the input; reason: every polynomial in these nonnegative quantities is bounded by such an expression
--   - encoding: finite undirected loopless graph, rational weights, binary input → `WGraph`, `encInput` (binary numbers, rationals in lowest terms); reason: Lean representation
-- source:
--   Xie, Sharp Power Loss Thresholds for Vector Min Uncut, STOC 2027 submission (manuscript sha256 391063da…), p. 35, Theorem 11

import Mathlib
import Definitions.Def_PowerMinUncut_Threshold_Machine

open MeasureTheory ProbabilityTheory Filter Topology

namespace PowerMinUncut.Threshold

open WGraph

/-- **Theorem 11 (bounded-bit integer-power rounding)**, p. 35. For integers `q ≥ 2` and `k > q`
there is one randomized Turing machine (a deterministic Cook machine reading fair coins) and
constants `c, d` such that, on every graph with nonnegative rational weights of total one and all
rationals `ζ > 0`, `0 < ω < 1`, on every coin string it halts within the bound
`c(1 + ℓ + N + |E| + max{1, 1/ζ} + 1 + log(1/ω))^d` and outputs nonzero `r_i ∈ ℚ^k` (output length
within the same bound, the random strings of that length), and with probability at least `1 - ω`
the cost at `v_i = r_i/√(r_i·r_i)` is at most `(C_{k,q} + ζ) OPT_{k,q}(G)`. -/
theorem theorem_11 (q k : ℕ) (hq : 2 ≤ q) (hk : q < k) :
    ∃ (Γ : Type) (_ : Fintype Γ) (ι : Sym ↪ Γ) (M : CookPvsNP.TM Γ) (c d : ℕ),
      IsRandRounding k q ι M c d := by sorry

end PowerMinUncut.Threshold
