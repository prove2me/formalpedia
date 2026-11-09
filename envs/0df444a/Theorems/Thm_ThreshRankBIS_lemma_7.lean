-- Prove2me | Theorems.Thm_ThreshRankBIS_lemma_7
-- name    : ThreshRankBIS.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:05:20.13121+00:00
-- url     : https://prove2.me/theorems/bf094a51-af52-4a84-94e5-98fc003872c3
-- title:
--   Lemma 7 — localization and recovery in time $2^{O(b+R+1)}\mathrm{poly}(n)\sum_{j\le\lfloor2R/d\rfloor}\binom{2n}{j}$
-- statement:
--   There is an algorithm and a constant $c>0$ with the following guarantee. Given a simple $d$-regular bipartite graph $G$ with $|X|=|Y|=n$, $d\ge1$, a vertex set $D_0\subseteq V(G)$ and integers $b,R\ge0$, it lists all maximal independent sets $I$ with
--
--   $$
--   |I|\ge n-b\qquad\text{and}\qquad|I\triangle D_0|\le R
--   $$
--
--   (and only these), in time at most
--
--   $$
--   c\,2^{c(b+R+1)}(n+1)^c\sum_{j=0}^{\min\{2n,\lfloor2R/d\rfloor\}}\binom{2n}{j}. \tag{8}
--   $$
--
--   Recovery turns each approximate cut into the exact maximal independent sets near it. Unlike earlier small-radius recovery, the bound does not require $R$ to be smaller than the degree, which the paper needs at small degrees.
--
--   Differences from the source:
--   - encoding: a simple d-regular bipartite graph G = (X ∪ Y, E) with |X| = |Y| = n and d ≥ 1 → the graph HiddenPartition.bip E of a biadjacency matrix E : Fin n → Fin n → Bool with all row and column sums d (IsRegular E d), 1 ≤ d and 0 < n; reason: every such graph is exactly one such matrix after numbering each side by Fin n; such a graph has n ≥ d ≥ 1, and 0 < n only excludes the empty matrix, which is vacuously d-regular
--   - encoding: a randomized algorithm and its running time in the bit model (p.17) → a CritWinSpin.RandMachine (Mathlib TM2 machine over Bool, uniform coin string, worst-case step bound over all coin strings), fixed with the O-constants before the graph and the inputs; reason: the paper's procedures are all capped (pp.7, 12), so the time is worst case; polynomial simulation overheads between machine models are absorbed by the polynomial factor
--   - encoding: input (G, D₀, b, R); output the list of maximal independent sets → input tupleCode [encGraph n E, encSet n D₀, encBin b, encBin R]; output encSetList n L (length in binary, then 2n-bit indicator strings); reason: standard encodings, polynomially related to any other
--   - reading: all maximal independent sets I with |I| ≥ n − b and |I △ D₀| ≤ R can be listed → for every coin string the output list L satisfies: I ∈ L iff I is maximal independent with |I| ≥ n − b and |I △ D₀| ≤ R (repetitions allowed); reason: the procedure keeps a candidate J only if it is such a set (Proof of Lemma 7, Recovery, p.10), so the stronger 'exactly these' reading holds; the procedure is deterministic, so it holds for every coin string
--   - encoding: 2^{O(b+R+1)} poly(n) → c·2^{c(b+R+1)}·(n+1)^c, c fixed before the input; reason: the usual unfolding of the O-notation; (n+1) avoids the degenerate base 0
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), Lemma 7, p.10, display (8)

import Mathlib
import Definitions.Def_ThreshRankBIS_countInput
import Definitions.Def_ThreshRankBIS_hardcoreZ
set_option autoImplicit false
open Finset QuantumPRC

namespace ThreshRankBIS

/-- **Lemma 7 (Localization and recovery)**, p.10. There is a machine and a constant `c > 0`
such that, given a `d`-regular bipartite `G` (`d ≥ 1`), `D_0 ⊆ V(G)` and integers `b, R ≥ 0`, it
lists the maximal independent sets `I` with `|I| ≥ n − b` and `|I △ D_0| ≤ R` (exactly these,
possibly with repetitions), for every coin string, in time at most
`c · 2^{c(b + R + 1)} (n + 1)^c ∑_{j=0}^{min{2n, ⌊2R/d⌋}} binom(2n, j)` (display (8)).

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), Lemma 7, p.10.

**Formalization Note.** The machine is the platform's `CritWinSpin.RandMachine` (a Mathlib `TM2`
machine over `Bool` with a worst-case step bound for every coin string); the procedure is
deterministic, so the output is correct for every coin string. Input `recoveryInput n E D0 b R`;
output `encSetList n L`. `2^{O(b+R+1)} poly(n)` is `c·2^{c(b+R+1)}(n+1)^c` with `c` independent
of the input; `|I| ≥ n − b` is an integer inequality; `⌊2R/d⌋` is natural-number division. -/
theorem lemma_7 :
    ∃ M : CritWinSpin.RandMachine, ∃ c : ℝ, 0 < c ∧
      ∀ (n d : ℕ) (E : Fin n → Fin n → Bool), IsRegular E d → 1 ≤ d → 0 < n →
      ∀ (D0 : Finset (V n)) (b R : ℕ),
        (∀ ω : Fin (M.coins (recoveryInput n E D0 b R)) → Bool,
          ∃ L : List (Finset (V n)),
            M.run (tupleCode [List.ofFn ω, recoveryInput n E D0 b R]) = encSetList n L ∧
            ∀ I : Finset (V n),
              I ∈ L ↔ (IsMaxIndep E I ∧ (n : ℤ) - b ≤ #I ∧ #(symmDiff I D0) ≤ R)) ∧
        (M.time (recoveryInput n E D0 b R) : ℝ) ≤
          c * (2 : ℝ) ^ (c * ((b : ℝ) + R + 1)) * ((n : ℝ) + 1) ^ c *
            ∑ j ∈ range (min (2 * n) (2 * R / d) + 1), ((2 * n).choose j : ℝ) := by sorry

end ThreshRankBIS
