-- Prove2me | Theorems.Thm_ThreshRankBIS_theorem_1
-- name    : ThreshRankBIS.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:07:48.523327+00:00
-- url     : https://prove2.me/theorems/4abb4bcf-5279-4506-a1de-23743d7de8e4
-- title:
--   Theorem 1 — approximate counting from threshold rank in time $2^{O(k)}(n+B+1/\epsilon)^{O(1)}$ when $d\ge C\log(n+1)$
-- statement:
--   Fix $0<\rho<1$ and $\lambda_0>0$. Let $C_{\rho,\lambda_0}$ be sufficiently large, and let $G=(X\cup Y,E)$ be a simple $d$-regular bipartite graph with $|X|=|Y|=n$ and
--
--   $$
--   d\ge C_{\rho,\lambda_0}\log(n+1). \tag{1}
--   $$
--
--   For every rational $\lambda\ge\lambda_0$ and $0<\epsilon\le1$, a randomized algorithm computes a relative $\epsilon$-approximation to $Z_G(\lambda)$ (an estimate $\hat Z$ with $e^{-\epsilon}Z_G(\lambda)\le\hat Z\le e^{\epsilon}Z_G(\lambda)$) with probability at least $3/4$ in time
--
--   $$
--   2^{O_{\rho,\lambda_0}(k)}\,(n+B+1/\epsilon)^{O_{\rho,\lambda_0}(1)}, \tag{2}
--   $$
--
--   where $k=k_\rho(G)=\#\{i:\lambda_i(A_G)\ge(1-\rho)d\}$ is the threshold rank (eigenvalues of the adjacency matrix counted with multiplicity) and $B$ is the combined binary encoding length of $\lambda$ and $\epsilon$. In particular, this gives an FPRAS when $k=O(\log n)$.
--
--   The exponential factor depends only on the threshold rank, and the degree condition does not depend on the accuracy. For graphs whose adjacency spectrum has $O(\log n)$ eigenvalues near the top this is a fully polynomial randomized approximation scheme for the hard-core partition function, including the number of independent sets (#BIS) at $\lambda=1$.
--
--   **Formalization Note** "Let $C$ be sufficiently large" is read as "there is $C>0$": the hypothesis (1) is monotone in $C$. One machine and one constant serve every graph and every input.
--
--   Differences from the source:
--   - encoding: a simple d-regular bipartite graph G = (X ∪ Y, E) with |X| = |Y| = n and d ≥ 1 → the graph HiddenPartition.bip E of a biadjacency matrix E : Fin n → Fin n → Bool with all row and column sums d (IsRegular E d), 1 ≤ d and 0 < n; reason: every such graph is exactly one such matrix after numbering each side by Fin n; such a graph has n ≥ d ≥ 1, and 0 < n only excludes the empty matrix, which is vacuously d-regular
--   - encoding: a randomized algorithm and its running time in the bit model (p.17) → a CritWinSpin.RandMachine (Mathlib TM2 machine over Bool, uniform coin string, worst-case step bound over all coin strings), fixed with the O-constants before the graph and the inputs; reason: the paper's procedures are all capped (pp.7, 12), so the time is worst case; polynomial simulation overheads between machine models are absorbed by the polynomial factor
--   - encoding: input (G, λ, ε) with λ, ε rational and B their combined binary encoding length; output an estimate Ẑ → input tupleCode [encGraph n E, encRat λ, encRat ε], B = bitLen λ ε = |encRat λ| + |encRat ε|; success requires the output string to be exactly encRat Ẑ for a rational Ẑ with e^{−ε}Z ≤ Ẑ ≤ e^{ε}Z; reason: standard encodings; bitLen is within a constant factor of any binary encoding length, absorbed by the polynomial factor; encRat is injective
--   - encoding: 2^{O(f)}·(n + B + 1/ε)^{O(1)} → c·2^{c·f}·(n + B + 1/ε)^c for one constant c > 0 chosen before the graph and inputs; reason: the usual unfolding of the O-notation with constants depending only on ρ, λ₀; the leading factor c is harmless since n + B + 1/ε ≥ 2
--   - reading: C_{ρ,λ₀} sufficiently large → ∃ C > 0, chosen together with the machine and the constants before the graph; reason: d ≥ C log(n+1) is monotone in C, so 'for all large C' and 'for some C' are the same theorem
--   - encoding: in particular, this gives an FPRAS when k = O(log n) → a second conjunct for the same machine and C: for every c′ > 0 there is c″ > 0 such that every valid input with k ≤ c′ log(n+1) runs in time ≤ c″(n + B + 1/ε)^{c″}; reason: together with the success probability of the first conjunct this is the definition of an FPRAS (p.3) on that class; log(n+1) keeps n = 1 non-degenerate
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), Theorem 1, p.3, displays (1)–(2); definitions §1.1, p.3

import Mathlib
import Definitions.Def_ThreshRankBIS_countInput
import Definitions.Def_ThreshRankBIS_hardcoreZ
import Definitions.Def_ThreshRankBIS_thresholdRank
set_option autoImplicit false
open Finset

namespace ThreshRankBIS

/-- **Theorem 1 (Approximate counting from threshold rank)**, p.3. Fix `0 < ρ < 1` and
`λ_0 > 0`. Let `C_{ρ,λ_0}` be sufficiently large, and suppose `d ≥ C_{ρ,λ_0} log(n + 1)` (1). For
every `λ ≥ λ_0` and `0 < ε ≤ 1`, a randomized algorithm computes a relative `ε`-approximation to
`Z_G(λ)` with probability at least `3/4` in time `2^{O_{ρ,λ_0}(k)}(n + B + 1/ε)^{O_{ρ,λ_0}(1)}` (2).
In particular, this gives an FPRAS when `k = O(log n)`.

Here `G = (X ∪ Y, E)` is a simple `d`-regular bipartite graph with `|X| = |Y| = n`,
`k = k_ρ(G) = #{i : λ_i(A_G) ≥ (1 − ρ)d}` counted with multiplicity, `λ, ε` are rational and `B`
is their combined binary encoding length (§1.1, p.3).

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), Theorem 1, p.3;
definitions §1.1, p.3.

**Formalization Note.** "Let `C` be sufficiently large" is `∃ C > 0` (the hypothesis
`d ≥ C log(n + 1)` is monotone in `C`). The algorithm is one `CritWinSpin.RandMachine` `M`,
chosen with `C` and the `O`-constant `c` after `ρ, λ_0` and before the graph and the inputs; its
running time is worst case over the coin string. Input `countInput n E λ ε`; success means the
output is exactly `encRat Ẑ` with `e^{−ε}Z_G(λ) ≤ Ẑ ≤ e^{ε}Z_G(λ)`. The time bound (2) is
`c·2^{ck}(n + B + 1/ε)^c`, `B = bitLen λ ε`. The second conjunct is the FPRAS clause for the same
machine: whenever `k ≤ c'log(n + 1)` the time is at most `c''(n + B + 1/ε)^{c''}`. -/
theorem theorem_1 (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (lam0 : ℝ) (hlam0 : 0 < lam0) :
    ∃ C : ℝ, 0 < C ∧ ∃ M : CritWinSpin.RandMachine, ∃ c : ℝ, 0 < c ∧
      (∀ (n d : ℕ) (E : Fin n → Fin n → Bool), IsRegular E d → 1 ≤ d → 0 < n →
        C * Real.log ((n : ℝ) + 1) ≤ d →
        ∀ lam : ℚ, lam0 ≤ lam → ∀ ε : ℚ, 0 < ε → ε ≤ 1 →
          3 / 4 ≤ successProb M (countInput n E lam ε) (goodCount (hardcoreZ E lam) ε) ∧
          (M.time (countInput n E lam ε) : ℝ) ≤
            c * (2 : ℝ) ^ (c * (thresholdRank ρ E d : ℝ)) *
              ((n : ℝ) + bitLen lam ε + 1 / (ε : ℝ)) ^ c) ∧
      (∀ c' : ℝ, 0 < c' → ∃ c'' : ℝ, 0 < c'' ∧
        ∀ (n d : ℕ) (E : Fin n → Fin n → Bool), IsRegular E d → 1 ≤ d → 0 < n →
          C * Real.log ((n : ℝ) + 1) ≤ d →
          (thresholdRank ρ E d : ℝ) ≤ c' * Real.log ((n : ℝ) + 1) →
          ∀ lam : ℚ, lam0 ≤ lam → ∀ ε : ℚ, 0 < ε → ε ≤ 1 →
            (M.time (countInput n E lam ε) : ℝ) ≤
              c'' * ((n : ℝ) + bitLen lam ε + 1 / (ε : ℝ)) ^ c'') := by sorry

end ThreshRankBIS
