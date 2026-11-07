-- Prove2me | Theorems.Thm_PathCount2k_lemma_2_6
-- name    : PathCount2k.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:46:26.813199+00:00
-- url     : https://prove2.me/theorems/d3cfa77c-0efa-420b-8361-43959143db2e
-- title:
--   Lemma 2.6 — accuracy and number of trials of the median of means
-- statement:
--   Set $D=k$, $C_k=3e^2K_k$, and for $0<\varepsilon,\delta<1$ choose $R=\lceil8C_k\varepsilon^{-2}\rceil$ and $q=2\lceil\log_2(1/\delta)\rceil+1$. Let $\hat N$ be the median of the $q$ group averages of $qR$ independent Gaussian trials $Y_{j,\ell}$ (Definition 2.10). Then
--   $$
--   \Pr\big[|\hat N-N|\le\varepsilon N\big]\ge1-\delta,
--   $$
--   and there is a universal constant $C_0$ with $Rq\le C_0\,k^2\varepsilon^{-2}\log(2/\delta)$.
--
--   This turns the variance bound into a $(1\pm\varepsilon)$-approximation with failure probability $\delta$.
--
--   Differences from the source:
--
--   - generalization: 2 ≤ k ≤ n (standing assumption of §2.1, p.4) → every k ≥ 1; reason: the statement is true for these k and n too (k > n gives N = 0); it specializes to the source's range
--   - generalization: a directed graph (no self-loops discussed) → the arc set may contain self-loops (v, v); reason: a path never uses a loop, so P_k and N are unchanged; on loop-free graphs the statement is the source's
--   - encoding: vertices v ∈ V, positions and coordinates 1, …, k → vertices Fin n, positions and coordinates Fin k (0-based); reason: relabelling; same instances
--   - encoding: g_v ∼ N(0, I_k) independent; entries of M_{i,v} standard Gaussian divided by √D, independent → vecLaw = Measure.pi of gaussianReal 0 1; matLaw = Measure.pi of gaussianReal 0 (1/D); jointLaw their product; reason: the law of X/√D for X ∼ N(0,1) is N(0, 1/D); same distributions
--   - reading: Rq = O(k²ε⁻² log(2/δ)) → ∃ C₀ : ℝ, quantified before every datum, with Rq ≤ C₀·k²·ε⁻²·log(2/δ); reason: the meaning of the O-notation in k, ε, δ
--   - encoding: Pr over the qR independent trials; median(Ȳ₁, …, Ȳ_q) → the product law momLaw n k k R q (measure of the event); the (⌊q/2⌋+1)-th smallest of the q averages; reason: q is odd, so this is the median; the event is measurable, so its measure is the probability
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Lemma 2.6, p.8 (with Corollary 2.1 and Definition 2.10)

import Mathlib
import Definitions.Def_PathCount2k_Graph
import Definitions.Def_PathCount2k_Exterior
import Definitions.Def_PathCount2k_Gaussian

open MeasureTheory ProbabilityTheory

namespace PathCount2k

/-- Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026), **Lemma 2.6** (Accuracy and number of trials), p.8: "For `0 < ε, δ < 1`, choose
`R = ⌈8C_k ε⁻²⌉` and `q = 2⌈log₂(1/δ)⌉ + 1`. Then we have `Pr[|N̂ − N| ≤ εN] ≥ 1 − δ`. The total
number of trials is `Rq = O(k² ε⁻² log(2/δ))`."

Here `C_k = 3e²K_k` (Corollary 2.1), `D = k` ("For the amplification procedure below, we set
`D = k`", p.8), and `N̂` is the median-of-means estimator of Definition 2.10 over `qR` independent
Gaussian trials.

**Formalization Note.** `Pr` is the product law `momLaw n k k R q` of the `qR` trials (outer
measure of the event). The `O(·)` is a universal constant `C₀`, quantified before every datum.
Stated for every `k ≥ 1` (the paper assumes `2 ≤ k ≤ n`, §2.1). -/
theorem lemma_2_6 :
    ∃ C₀ : ℝ, ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (k : ℕ), 1 ≤ k →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        (momLaw n k k ⌈8 * Ck k / ε ^ 2⌉₊ (2 * ⌈Real.logb 2 (1 / δ)⌉₊ + 1)).real
            {ω | |momNhat n E k k ⌈8 * Ck k / ε ^ 2⌉₊ (2 * ⌈Real.logb 2 (1 / δ)⌉₊ + 1) ω -
                (N n E k : ℝ)| ≤ ε * (N n E k : ℝ)} ≥ 1 - δ ∧
          ((⌈8 * Ck k / ε ^ 2⌉₊ : ℝ) * ((2 * ⌈Real.logb 2 (1 / δ)⌉₊ + 1 : ℕ) : ℝ)) ≤
            C₀ * (k : ℝ) ^ 2 * ε ^ (-2 : ℤ) * Real.log (2 / δ) := by sorry

end PathCount2k
