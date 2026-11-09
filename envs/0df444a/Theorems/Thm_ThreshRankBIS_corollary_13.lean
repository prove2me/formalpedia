-- Prove2me | Theorems.Thm_ThreshRankBIS_corollary_13
-- name    : ThreshRankBIS.corollary_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:05:18.940484+00:00
-- url     : https://prove2.me/theorems/70bf275c-0741-437e-9401-0546f3990591
-- title:
--   Corollary 13 — counting and sampling at every degree in time $2^{O(k+ne^{-ad})}(n+B+1/\epsilon)^{O(1)}$
-- statement:
--   Fix $0<\rho<1$ and $\lambda_0>0$. There is a constant $a>0$ such that, for every simple $d$-regular bipartite graph $G$ with $|X|=|Y|=n$ and $d\ge1$ and every rational $\lambda\ge\lambda_0$ and $0<\epsilon\le1$, the counting and sampling algorithms achieve the accuracy guarantees of Theorem 1 and Corollary 2 in time
--
--   $$
--   2^{O_{\rho,\lambda_0}(k+ne^{-ad})}\,(n+B+1/\epsilon)^{O_{\rho,\lambda_0}(1)},
--   $$
--
--   where $k=k_\rho(G)$ and $B$ is the combined binary encoding length of $\lambda$ and $\epsilon$. That is, the counting algorithm outputs a relative $\epsilon$-approximation to $Z_G(\lambda)$ with probability at least $3/4$, and the sampling algorithm outputs an independent set with a law $\hat\mu$ satisfying $\|\hat\mu-\mu_{G,\lambda}\|_{TV}\le\epsilon$. Taking $\rho=1/2$ gives $\exp(O_{\lambda_0}(n/d))(n+B+1/\epsilon)^{O_{\lambda_0}(1)}$ time.
--
--   This is the paper's all-degree bound; at sufficiently large logarithmic degree $ne^{-ad}=O(1)$ and it gives Theorem 1, and with $\rho=1/2$ it improves the exponent of the Jenssen–Perkins–Potukuchi algorithm.
--
--   Differences from the source:
--   - encoding: a simple d-regular bipartite graph G = (X ∪ Y, E) with |X| = |Y| = n and d ≥ 1 → the graph HiddenPartition.bip E of a biadjacency matrix E : Fin n → Fin n → Bool with all row and column sums d (IsRegular E d), 1 ≤ d and 0 < n; reason: every such graph is exactly one such matrix after numbering each side by Fin n; such a graph has n ≥ d ≥ 1, and 0 < n only excludes the empty matrix, which is vacuously d-regular
--   - encoding: a randomized algorithm and its running time in the bit model (p.17) → a CritWinSpin.RandMachine (Mathlib TM2 machine over Bool, uniform coin string, worst-case step bound over all coin strings), fixed with the O-constants before the graph and the inputs; reason: the paper's procedures are all capped (pp.7, 12), so the time is worst case; polynomial simulation overheads between machine models are absorbed by the polynomial factor
--   - encoding: input (G, λ, ε) with λ, ε rational and B their combined binary encoding length; output an estimate Ẑ → input tupleCode [encGraph n E, encRat λ, encRat ε], B = bitLen λ ε = |encRat λ| + |encRat ε|; success requires the output string to be exactly encRat Ẑ for a rational Ẑ with e^{−ε}Z ≤ Ẑ ≤ e^{ε}Z; reason: standard encodings; bitLen is within a constant factor of any binary encoding length, absorbed by the polynomial factor; encRat is injective
--   - encoding: the sampling algorithm outputs an independent set with distribution µ̂ → the sampler reads the same input string; its output law is decoded by decSet n (2n-bit indicator strings), and total variation is taken over all outcomes including undecodable outputs; reason: any output that is not the code of an independent set counts against the sampler
--   - encoding: 2^{O(f)}·(n + B + 1/ε)^{O(1)} → c·2^{c·f}·(n + B + 1/ε)^c for one constant c > 0 chosen before the graph and inputs; reason: the usual unfolding of the O-notation with constants depending only on ρ, λ₀; the leading factor c is harmless since n + B + 1/ε ≥ 2
--   - encoding: taking ρ = 1/2 gives exp(O_{λ₀}(n/d))(n + B + 1/ε)^{O_{λ₀}(1)} time → a second conjunct: for every λ₀ > 0 there are counting and sampling machines and c > 0 with the same guarantees and times ≤ c·exp(c·n/d)(n + B + 1/ε)^c; reason: the clause is a statement about ρ = 1/2 with constants depending on λ₀ only
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), Corollary 13, p.16; Corollary 2, p.3; §1.1, p.3

import Mathlib
import Definitions.Def_ThreshRankBIS_countInput
import Definitions.Def_ThreshRankBIS_hardcoreZ
import Definitions.Def_ThreshRankBIS_thresholdRank
set_option autoImplicit false
open Finset

namespace ThreshRankBIS

/-- **Corollary 13 (Counting and sampling at every degree)**, p.16. Fix `0 < ρ < 1` and
`λ_0 > 0`. There is a constant `a > 0` such that, for every simple `d`-regular bipartite graph
with `d ≥ 1` and every rational `λ ≥ λ_0` and `0 < ε ≤ 1`, the counting and sampling algorithms
achieve the accuracy guarantees of Theorem 1 (a relative `ε`-approximation to `Z_G(λ)` with
probability at least `3/4`) and Corollary 2 (an output law `µ̂` with `‖µ̂ − µ_{G,λ}‖_TV ≤ ε`) in
time `2^{O_{ρ,λ_0}(k + ne^{−ad})}(n + B + 1/ε)^{O_{ρ,λ_0}(1)}`. Taking `ρ = 1/2` gives
`exp(O_{λ_0}(n/d))(n + B + 1/ε)^{O_{λ_0}(1)}` time.

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), Corollary 13, p.16;
Corollary 2, p.3 (the sampling guarantee); §1.1, p.3 (relative approximation, total variation).

**Formalization Note.** Both algorithms are `CritWinSpin.RandMachine`s, fixed (with `a` and the
`O`-constant `c`) before the graph and the inputs, with worst-case running time; both read
`countInput n E λ ε`. The counting output must be the string `encRat Ẑ`; the sampler's output is
decoded by `decSet n`, and undecodable outputs (`none`) and non-independent sets count against
it in total variation. `B = bitLen λ ε`. The second conjunct is the `ρ = 1/2` clause, with its own
machines and constant depending on `λ_0` only. -/
theorem corollary_13 :
    (∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ lam0 : ℝ, 0 < lam0 →
      ∃ a : ℝ, 0 < a ∧ ∃ Mc Ms : CritWinSpin.RandMachine, ∃ c : ℝ, 0 < c ∧
        ∀ (n d : ℕ) (E : Fin n → Fin n → Bool), IsRegular E d → 1 ≤ d → 0 < n →
        ∀ lam : ℚ, lam0 ≤ lam → ∀ ε : ℚ, 0 < ε → ε ≤ 1 →
          3 / 4 ≤ successProb Mc (countInput n E lam ε) (goodCount (hardcoreZ E lam) ε) ∧
          tv (CritWinSpin.outLaw Ms (countInput n E lam ε) (decSet n)) (gibbs E lam) ≤ ε ∧
          (Mc.time (countInput n E lam ε) : ℝ) ≤
            c * (2 : ℝ) ^ (c * ((thresholdRank ρ E d : ℝ) + n * Real.exp (-(a * d)))) *
              ((n : ℝ) + bitLen lam ε + 1 / (ε : ℝ)) ^ c ∧
          (Ms.time (countInput n E lam ε) : ℝ) ≤
            c * (2 : ℝ) ^ (c * ((thresholdRank ρ E d : ℝ) + n * Real.exp (-(a * d)))) *
              ((n : ℝ) + bitLen lam ε + 1 / (ε : ℝ)) ^ c) ∧
    (∀ lam0 : ℝ, 0 < lam0 →
      ∃ Mc Ms : CritWinSpin.RandMachine, ∃ c : ℝ, 0 < c ∧
        ∀ (n d : ℕ) (E : Fin n → Fin n → Bool), IsRegular E d → 1 ≤ d → 0 < n →
        ∀ lam : ℚ, lam0 ≤ lam → ∀ ε : ℚ, 0 < ε → ε ≤ 1 →
          3 / 4 ≤ successProb Mc (countInput n E lam ε) (goodCount (hardcoreZ E lam) ε) ∧
          tv (CritWinSpin.outLaw Ms (countInput n E lam ε) (decSet n)) (gibbs E lam) ≤ ε ∧
          (Mc.time (countInput n E lam ε) : ℝ) ≤
            c * Real.exp (c * n / d) * ((n : ℝ) + bitLen lam ε + 1 / (ε : ℝ)) ^ c ∧
          (Ms.time (countInput n E lam ε) : ℝ) ≤
            c * Real.exp (c * n / d) * ((n : ℝ) + bitLen lam ε + 1 / (ε : ℝ)) ^ c) := by sorry

end ThreshRankBIS
