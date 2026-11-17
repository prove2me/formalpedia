-- Prove2me | Theorems.Thm_SuperlatSVP_Supplement_theorem_3_6
-- name    : SuperlatSVP.Supplement.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:37:22.440134+00:00
-- url     : https://prove2.me/theorems/0f78178e-9b66-4ae6-a70e-e8f7fad7066c
-- title:
--   Theorem 3.6 — restriction lower bound on $\mathbb Z^n$ at $t=n^{-1/2}$, $\mathbb E[M]\ge(\frac23\varepsilon-o(1))\chi^n$ and $\mathbb E[\#\mathrm{calls}]\ge(\frac23\varepsilon-o(1))\chi^n/N$
-- statement:
--   **Theorem 3.6 (lower bound for restriction).** Fix $\chi\ge1$, $0<\varepsilon\le1$ and an integer $N\ge1$. There is a sequence $e(n)\to0$ with the following property.
--
--   For every $n\ge1$, let $t=n^{-1/2}$. Consider any randomized adaptive procedure that repeatedly chooses a superlattice $\Lambda\supseteq\mathbb Z^n$ with $\eta_{1/2}(\Lambda)\le t$ and receives at most $N$ fresh independent samples from $D_{\Lambda,\chi t}$ per call. If its probability of outputting a received sample lying in $\mathbb Z^n$ is at least $\varepsilon$, then
--   $$\mathbb E[M]\ \ge\ \Big(\tfrac23\varepsilon-e(n)\Big)\chi^n
--   \qquad\text{and}\qquad
--   \mathbb E[\#\text{calls}]\ \ge\ \Big(\tfrac23\varepsilon-e(n)\Big)\frac{\chi^n}{N},$$
--   where $M$ is the total number of received samples.
--
--   So sampling by restriction from smooth superlattices cannot beat $\chi^n$ samples, even on $\mathbb Z^n$ and even when the procedure adapts. With $\chi=\sqrt2$, the width loss of the ADRS sampler, constant success needs $\Omega(2^{n/2})$ samples, which matches Theorem 3.4.
--
--   **Formalization Note** Procedures, success, $\mathbb E[M]$ and the expected number of calls are those of `SuperlatSVP.Supplement.Admissible`. Expectations lie in $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: procedures that adaptively choose superlattices and "output only a received sample in L" → any behavioural randomized adaptive procedure, which may also output a non-received point or nothing, abort, or run forever; success counts only outputs of a received sample in ℤⁿ; reason: the class contains every procedure of the theorem, with the same success probability and expectations, so the Lean statement specializes to the source's.
--   - encoding: the o(1) terms → one sequence e(n) → 0 chosen after χ, ε, N and before n and the procedure; reason: this is how "o(1)" for fixed χ, ε, N reads (p.14, constants uniform).
--   - encoding: superlattices Λ ⊇ ℤⁿ → lattices L(C) of invertible rational matrices C containing ℤⁿ; samples as rational vectors; reason: every superlattice of ℤⁿ is of this form and its points are rational.
--   - encoding: N ≥ 1 → a natural number N ≥ 1; reason: the number of samples per call is an integer, so "at most N" means at most ⌊N⌋, and the bound χⁿ/⌊N⌋ for the natural number ⌊N⌋ ≥ 1 implies the bound χⁿ/N for a real N ≥ 1.
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §3.2, p.28 (PDF p.28), Theorem 3.6; Proposition 3.5, p.26

import Mathlib
import Definitions.Def_SuperlatSVP_Supplement_Admissible

open Filter
open scoped ENNReal

namespace SuperlatSVP.Supplement

/-- Theorem 3.6 (Lower bound for restriction). Hhan, Kim, Kim, Laarhoven, *Superlattice methods for
the shortest vector problem and discrete Gaussian sampling*, STOC 2027 submission (manuscript
sha256 fcf5b14f…ba), §3.2, p.28 (PDF p.28): "Fix χ ≥ 1, 0 < ε ≤ 1, and N ≥ 1, and let L = Zⁿ and
t = n^{−1/2}. Consider a procedure that adaptively chooses superlattices Λi ⊇ L with
η1/2(Λi) ≤ t, receives at most N fresh independent samples from DΛi,χt per call, and outputs only a
received sample in L. Success probability at least ε requires, in expectation, at least
(2/3 ε − o(1)) χⁿ samples and (2/3 ε − o(1)) χⁿ/N calls."

**Formalization Note.** The `o(1)` is one sequence `e(n) → 0`, chosen after `χ, ε, N` and before
the dimension `n` and the procedure. For every `n ≥ 1` and every admissible randomized adaptive
procedure `σ` (`Admissible σ t N` with `t = 1/√n`: superlattices `Λ ⊇ ℤⁿ` with `η_{1/2}(Λ) ≤ t`, at
most `N` samples per call, unboundedly many calls), served fresh independent samples from
`D_{Λ,χt}`, success probability `≥ ε` (`successProb`: it outputs a received sample in `ℤⁿ`) implies
`E[M] ≥ (2ε/3 − e(n))χⁿ` and `E[#calls] ≥ (2ε/3 − e(n))χⁿ/N`, with expectations in `[0, ∞]`
(`expSamples`, `expCalls`). The coefficient is `(2/3)·ε`. -/
theorem theorem_3_6 (χ : ℝ) (hχ : 1 ≤ χ) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (N : ℕ)
    (hN : 1 ≤ N) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (nhds 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ σ : RStrategy n, Admissible σ (1 / Real.sqrt n) N →
        ENNReal.ofReal ε ≤ successProb σ (χ * (1 / Real.sqrt n)) →
          ENNReal.ofReal ((2 / 3 * ε - e n) * χ ^ n) ≤ expSamples σ (χ * (1 / Real.sqrt n)) ∧
          ENNReal.ofReal ((2 / 3 * ε - e n) * χ ^ n / N) ≤
            expCalls σ (χ * (1 / Real.sqrt n)) := by sorry

end SuperlatSVP.Supplement
