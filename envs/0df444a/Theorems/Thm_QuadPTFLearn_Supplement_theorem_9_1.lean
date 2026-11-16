-- Prove2me | Theorems.Thm_QuadPTFLearn_Supplement_theorem_9_1
-- name    : QuadPTFLearn.Supplement.theorem_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:43:00.914177+00:00
-- url     : https://prove2.me/theorems/cb7ba866-c8f7-4e92-af9c-926f1f053311
-- title:
--   Theorem 9.1, p.81 (corrected: log(2/δ) for log(1/δ)) — PAC learning $\mathcal H_k$ w.p. $1-\delta$ with $d^{O(k)}2^{O_k(\log^3(1/\varepsilon))}\log(2/\delta)$ samples and time
-- statement:
--   **Learning by dimension reduction and hinge loss.** Let $\mathcal H_k$ be the class of intersections $f^*(x)=1\{q_1(x)\ge0,\dots,q_k(x)\ge0\}$ of $k$ polynomial threshold functions of degree at most two on $\mathbb R^d$. There are one algorithm, a universal constant $C$ and constants $C_k$ depending only on $k$ with the following guarantee. For all $k,d\ge1$, all $\varepsilon,\delta\in(0,1)$ and every target $f^*\in\mathcal H_k$, the algorithm is given i.i.d. examples $(x,f^*(x))$ with $x\sim N(0,I_d)$. It draws at most
--   $$C\,d^{Ck}\,2^{C_k\log^3(1/\varepsilon)}\,\log(2/\delta)$$
--   samples and runs within the same number of arithmetic operations. With probability at least $1-\delta$ it outputs a hypothesis $\hat h:\mathbb R^d\to\{0,1\}$, a polynomial threshold function of learned quadratic features, with
--   $$\mathrm{err}(\hat h)=\Pr_{x\sim N(0,I_d)}[\hat h(x)\ne f^*(x)]\le\varepsilon .$$
--
--   This is the formal, confidence-explicit version of the main result (Theorem 1.3, the case $\delta=1/100$, $\varepsilon<1/2$). The paper prints the factor $\log(1/\delta)$, which cannot be right as $\delta\to1$; $\log(2/\delta)$ agrees with it up to a factor $2$ for $\delta\le1/2$.
--
--   **Formalization Note** The machine, sample law, error and output layout are those of the published `QuadPTFLearn.theorem_1_3`. The program and the constants $C$, $C_k$ are chosen before $k$, $d$, $\varepsilon$, $\delta$ and the target, and logarithms are natural.
--
--   Differences from the source:
--   - correction: d^{O(k)}2^{O_k(log³(1/ϵ))} log(1/δ) samples and time → C·d^{Ck}·2^{Ck(k)·log³(1/ε)}·log(2/δ); reason: as printed the bound tends to 0 as δ → 1. Counterexample: k = d = 1, ε = 1/4, δ close enough to 1 that the bound is < 1; the run then reads no sample (and cannot even execute halt), so its output is fixed, while the targets q ≡ 1 and q ≡ −1 are at Gaussian distance 1 and no fixed hypothesis has error ≤ 1/4 against both, although probability 1 − δ > 0 is required. log(2/δ) is within a factor 2 of log(1/δ) for δ ≤ 1/2, so the claim for δ ≤ 1/2 is unchanged; the proof's own bound has log²(2/δ) (p.93), which is not adopted
--   - reading: "there is an algorithm … uses/draws … samples, runs in … time", model unspecified → one admissible program of the deterministic arithmetic sampling real RAM (exact + − × ÷, comparisons, pointers; no √, exp, log, floor, coin; unit cost, `sample` costs d+1), chosen before every parameter and the distribution, with samples and work bounded on every sample stream; reason: the paper fixes no model and its proofs count arithmetic operations; a single uniform program with worst-case bounds is the non-weaker reading (the convention of the published theorem_1_3)
--   - encoding: d^{O(k)}2^{O_k(log³(1/ϵ))}·(…) samples, … time → samples ≤ C·d^{Ck}·2^{Ck(k)·log³(1/ε)}·log(2/δ) and work ≤ the same, natural log, C universal and Ck chosen before k, d, ε, δ; reason: the meaning of O(k) and O_k(·) (§2); the leading C is the O's constant, needed because log³(1/ε) → 0 as ε → 1
--   - generalization: outputs a hypothesis ĥ : ℝᵈ → {0, 1} → output memory that decodes to f̂(x) = 1{Σ_t a_t ∏_j ϕ_j(x)^{e_{t,j}} ≥ 0} with quadratic features ϕ_j; an undecodable output is a failure; reason: this is the form Algorithm 6 returns (step 12, a PTF of the lifted features) and the output form stated on p.3; every such f̂ is a hypothesis, so the statement specializes to Theorem 9.1
--   - encoding: learning an intersection of k degree-2 PTFs under a Gaussian distribution (Definition 1.2: D with D_x = N(0, I_d), y = f*(x) a.s.); err_D(ĥ) → the i.i.d. stream of (x, f*(x)), x ∼ N(0, I_d), f* = ptfInd q with deg q_i ≤ 2; err = Pr_{x∼N(0,I)}[ĥ(x) ≠ f*(x)]; reason: every D of Definition 1.2 has exactly this sample law and this error (as in the published theorem_1_3)
--   - encoding: with probability at least 1 − δ → a measurable set of sample streams of probability ≥ 1 − δ on which every halted state decodes to a hypothesis of error ≤ ε; reason: the same event
--   - encoding: k ∈ ℤ₊ and an ambient dimension d → 1 ≤ k and 1 ≤ d; reason: ℤ₊ (Definition 1.1); ℝ⁰ has no inputs and d^{Ck} vanishes there
--   - encoding: given any ϵ, δ ∈ (0, 1) (and the class H_k) → input list [k, ε, δ] in memory from cell 0, d + 1 in pointer register 0, output read from the base address p[1]; reason: input and output convention of the machine; one program serves every k
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Theorem 9.1 (Learning by dimension reduction and hinge loss), p.81 (PDF p.83); Definitions 1.1, 1.2, p.2 (PDF p.4); Algorithm 6, p.94 (PDF p.96); proof pp.91–93 (PDF pp.93–95)

import Mathlib
import Definitions.Def_QuadPTFLearn_Learner

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

namespace Supplement

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Theorem 9.1 (Learning by dimension reduction and hinge loss), p.81 (PDF p.83), corrected:
`log(2/δ)` for `log(1/δ)`; with Definitions 1.1 and 1.2, p.2 (PDF p.4), and Algorithm 6, p.94.

There is one admissible program `P`, a universal constant `C` and a function `Ck` such that for
every `k, d ≥ 1`, all `ε, δ ∈ (0, 1)` and every target `f* = 1{q₁ ≥ 0, …, q_k ≥ 0}` with
`deg qᵢ ≤ 2`, run on input `[k, ε, δ]` and the i.i.d. stream of examples `(x, f*(x))`,
`x ∼ N(0, I_d)`:
1. on every stream it halts after at most `C d^{Ck} 2^{Ck(k) log³(1/ε)} log(2/δ)` samples and work;
2. with probability at least `1 − δ` its output decodes to a hypothesis `f̂ = 1{P(ϕ₁, …, ϕ_m) ≥ 0}`
   of quadratic features with `Pr_{x∼N(0,I)}[f̂(x) ≠ f*(x)] ≤ ε`.

**Formalization Note.** `P`, `C`, `Ck` are chosen before `k, d, ε, δ` and the target; logarithms
are natural. The leading `C` is the constant of the `O(·)`, needed since `log³(1/ε) → 0` as
`ε → 1`. The sample law and error are `sampleLaw q` and `err q`, the output layout `decode`, all
exactly as in the published `QuadPTFLearn.theorem_1_3`. -/
theorem theorem_9_1 :
    ∃ P : Program, Admissible P ∧ ∃ C : ℕ, ∃ Ck : ℕ → ℕ,
      ∀ k d : ℕ, 1 ≤ k → 1 ≤ d → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∀ q : Fin k → Poly d, IsQuadFamily q →
        HaltsWithin P (d + 1) (initState (d + 1) [(k : ℝ), ε, δ])
            (C * bound C Ck d k ε * Real.log (2 / δ))
            (C * bound C Ck d k ε * Real.log (2 / δ)) ∧
        SucceedsWP P (d + 1) (initState (d + 1) [(k : ℝ), ε, δ])
          (Measure.infinitePi (fun _ : ℕ => sampleLaw q)) (ENNReal.ofReal (1 - δ))
          (fun s => ∃ H : Hyp d, decode d (outMem s) (outBase s) = some H ∧
            err q H.eval ≤ ENNReal.ofReal ε) := by sorry

end Supplement

end QuadPTFLearn
