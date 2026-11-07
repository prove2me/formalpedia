-- Prove2me | Theorems.Thm_QuadPTFLearn_theorem_1_3
-- name    : QuadPTFLearn.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:25:06.15988+00:00
-- url     : https://prove2.me/theorems/e120fc2e-27f3-4931-a355-df532ed6db21
-- title:
--   Theorem 1.3, p.2 — PAC learning $\mathcal H_k$ under $N(0,I_d)$ to error $\varepsilon$ w.p. 99% with $d^{O(k)}2^{O_k(\log^3(1/\varepsilon))}$ samples and time
-- statement:
--   **Main algorithmic result.** There is an algorithm that PAC learns $\mathcal H_k$, the intersections $f^*(x)=1\{q_1(x)\ge0,\dots,q_k(x)\ge0\}$ of $k$ polynomial threshold functions of degree at most two, under the standard Gaussian distribution.
--
--   Precisely: there are one program $\mathcal A$ and constants $C$ (universal) and $C_k$ (depending on $k$ only) such that for all $k,d\ge1$, every $\varepsilon\in(0,1/2)$ and every target $f^*\in\mathcal H_k$ on $\mathbb R^d$, the program run on input $(k,\varepsilon)$ with i.i.d. examples $(x,f^*(x))$, $x\sim N(0,I_d)$:
--
--   1. on every sample sequence halts after at most
--   $$d^{Ck}\,2^{C_k\log^3(1/\varepsilon)}$$
--   samples and arithmetic operations;
--   2. with probability at least $99/100$ outputs a hypothesis $\hat f(x)=1\{P(\phi_1(x),\dots,\phi_m(x))\ge0\}$, a polynomial threshold function of learned quadratic features $\phi_j$, with
--   $$\mathrm{err}(\hat f)=\Pr_{x\sim N(0,I_d)}[\hat f(x)\ne f^*(x)]\le\varepsilon .$$
--
--   The exponent of $d$ is linear in $k$ and does not depend on $\varepsilon$; already for $k=2$ the previously known route, polynomial regression, costs $d^{O(1/\varepsilon^2)}$.
--
--   **Formalization Note** The machine is `QuadPTFLearn.Machine`; the output layout and the bound are those of `QuadPTFLearn.Learner`. The constants are chosen with the program, before $k$, $d$, $\varepsilon$ and the target.
--
--   Differences from the source:
--   - encoding: an unknown D on ℝᵈ × {0,1} with D_x = N(0, I_d) and y = f*(x) a.s.; err_D(f̂) = Pr_D[f̂(x) ≠ y] → the i.i.d. stream of (x, f*(x)), x ∼ N(0, I_d), and err = Pr_{x∼N(0,I)}[f̂(x) ≠ f*(x)]; reason: every D of Definition 1.2 has exactly this sample law and this error
--   - encoding: d^{O(k)} 2^{O_k(log³(1/ε))} samples and time → samples ≤ d^{Ck}·2^{Ck(k)·log³(1/ε)} and work ≤ the same, natural log, C universal and Ck chosen before k, d, ε; reason: the meaning of O(k) and O_k(·) (§2, p.13); one pair of constants for both bounds is equivalent to two pairs
--   - reading: "there is an algorithm … using … samples and time", model unspecified → one admissible program of the deterministic arithmetic sampling real RAM (exact + − × ÷, comparisons, pointers; no √, exp, log, floor, coin; unit cost, `sample` costs d+1), chosen before every parameter and the distribution, with samples and work bounded on every sample stream; reason: the paper fixes no model and its proofs count arithmetic operations; a single uniform program with worst-case bounds is the non-weaker reading
--   - generalization: output a hypothesis f̂ : ℝᵈ → {0,1} → output memory that decodes to f̂(x) = 1{Σ_t a_t ∏_j ϕ_j(x)^{e_{t,j}} ≥ 0} with quadratic features ϕ_j; an undecodable output is a failure; reason: this is the output form the paper states for its algorithm (p.3); every such f̂ is a hypothesis, so the statement specializes to Theorem 1.3
--   - encoding: with probability at least 99% → a measurable set of sample streams of probability ≥ 99/100 on which every halted state decodes to a hypothesis of error ≤ ε; reason: the same event
--   - encoding: k ∈ ℤ₊ and an ambient dimension d → 1 ≤ k and 1 ≤ d; reason: ℤ₊; ℝ⁰ has no inputs and the bound d^{Ck} vanishes there
--   - encoding: k indexes the class H_k; given an accuracy parameter ϵ; output a hypothesis → input list [k, ε] in memory from cell 0, d + 1 in pointer register 0, output read from the base address p[1]; reason: input and output convention of the machine; k as an input is what lets one program serve every k
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Theorem 1.3 (Main algorithmic result), with Definitions 1.1, 1.2, p.2 (PDF p.4); output form p.3 (PDF p.5)

import Mathlib
import Definitions.Def_QuadPTFLearn_Learner

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Theorem 1.3 (Main algorithmic result), p.2 (PDF p.4), with Definition 1.2, p.2.

There is one admissible program `P` of the arithmetic sampling real RAM, a universal constant
`C` and a function `Ck` such that for every `k, d ≥ 1`, every `ε ∈ (0, 1/2)` and every target
`f* = 1{q₁ ≥ 0, …, q_k ≥ 0}` with `deg qᵢ ≤ 2`, run on input `[k, ε]` and the i.i.d. stream of
labelled examples `(x, f*(x))`, `x ∼ N(0, I_d)`:
1. on every stream it halts after at most `d^{Ck} 2^{Ck(k) log³(1/ε)}` samples and work;
2. with probability at least `99/100` its output decodes to a hypothesis
   `f̂ = 1{P(ϕ₁, …, ϕ_m) ≥ 0}` of quadratic features with `Pr_{x∼N(0,I)}[f̂(x) ≠ f*(x)] ≤ ε`.

**Formalization Note.** The program is chosen before `k`, `d`, `ε` and the target, and `C`, `Ck`
before `k`, `d`, `ε` (one algorithm for the whole class, `O(k)` with a universal constant,
`O_k(·)` with a `k`-dependent one). The machine (`QuadPTFLearn.Machine`) has exact field
arithmetic, comparisons and pointers, no square root, floor or coin; `sample` costs `d + 1`.
The sample law of every `D` of Definition 1.2 is `sampleLaw q`. The output layout is that of
`decode` (p.3's PTF of learned quadratic features); an undecodable output is a failure. -/
theorem theorem_1_3 :
    ∃ P : Program, Admissible P ∧ ∃ C : ℕ, ∃ Ck : ℕ → ℕ,
      ∀ k d : ℕ, 1 ≤ k → 1 ≤ d → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∀ q : Fin k → Poly d, IsQuadFamily q →
        HaltsWithin P (d + 1) (initState (d + 1) [(k : ℝ), ε])
            (bound C Ck d k ε) (bound C Ck d k ε) ∧
        SucceedsWP P (d + 1) (initState (d + 1) [(k : ℝ), ε])
          (Measure.infinitePi (fun _ : ℕ => sampleLaw q)) (99 / 100)
          (fun s => ∃ H : Hyp d, decode d (outMem s) (outBase s) = some H ∧
            err q H.eval ≤ ENNReal.ofReal ε) := by sorry

end QuadPTFLearn
