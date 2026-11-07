-- Prove2me | Theorems.Thm_QMCBeyondHK_theorem_1_2
-- name    : QMCBeyondHK.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:31.477695+00:00
-- url     : https://prove2.me/theorems/f8885855-6a7b-4d8a-8ae9-cc9784ce9902
-- title:
--   Theorem 1.2 — uniformly-shifted Haar-thinning keeps $n$ of $(1+\varepsilon)n$ samples with $\mathbb E[\mathrm{err}(A_s,f)^2] \le C_d N_\ell^2\varepsilon^{-2}\sigma_{SO}(f)^2/n^2$
-- statement:
--   There are an absolute constant $c > 0$ and constants $C_d$ depending only on $d$ such that the following holds for every $d \ge 1$, $\varepsilon \in (0,1)$ and $n \ge 1$. Let $\ell = \lceil 10\log_2 n\rceil$, $N_\ell = (\ell+1)^d$, and run the uniformly-shifted Haar-thinning algorithm for $n$ steps on an independent uniform shift $s$ and input stream $(x_t,\xi_t,y_t)$; let $A_s$ be its $n$ retained samples.
--
--   1. **Sample budget.** The probability that the algorithm consumes more than $(1+\varepsilon)n$ samples is at most $e^{-c\varepsilon n}$.
--   2. **Beyond-Hardy–Krause error.** For every $f \in L^2([0,1)^d)$ with finite $\sigma_{SO}(f)$,
--   $$
--   \mathbb E\big[\operatorname{err}(A_s, f)^2\big] \le C_d\, \frac{N_\ell^2}{\varepsilon^2}\, \frac{\sigma_{SO}(f)^2}{n^2} = \tilde O_{d,\varepsilon}\big(\sigma_{SO}^2(f)/n^2\big).
--   $$
--   3. **Never two consecutive discards.** At every step $t < n$ the retained sample is $x_t$ if $x_t$ is accepted, and otherwise the next sample $y_t$.
--   4. **Online.** Whether $x_t$ is accepted, and the sample retained at step $t$, depend only on $s$ and the inputs of steps $\le t$.
--   5. **Per-sample work.** At every point of $[0,1)^d$ at most $N_\ell = O_d(\log^d n)$ Haar functions of $\Pi_{\le\ell}$ are nonzero, so each step evaluates a sum of at most $N_\ell$ terms; and retaining a point changes the discrepancy $\varphi(H)$ only for Haar functions $H$ that are nonzero at it.
--
--   This answers the question of Bansal and Jiang: the beyond-Hardy–Krause error bound needs only $(1+\varepsilon)n$ samples instead of $n^2$.
--
--   Differences from the source:
--   - reading: there is a randomized algorithm → the explicit uniformly-shifted Haar-thinning algorithm of §3.1 with ℓ = ⌈10 log₂ n⌉; reason: the algorithm §3 constructs and analyzes; the statement for it implies the existential one
--   - generalization: Õ_{d,ε}(σ²_SO(f)/n²) → C_d · N_ℓ² · ε⁻² · σ_SO(f)²/n² with C_d depending on d only; reason: an explicit member of Õ_{d,ε} (poly(1/ε) and O(log n)^{2d}, footnotes 3–4), the factor §3 proves; the log^d n / log^{d+1} n refinements of footnote 4 and p.8 are not proved in the paper
--   - reading: takes as input (1 + ε)n i.i.d. uniform samples and outputs with high probability a subset of n samples → the algorithm reads an unbounded independent uniform stream; it consumes more than (1 + ε)n samples with probability ≤ exp(−cεn), c absolute; the error expectation is over the whole run, unconditioned; reason: Proposition 2.4 pins 'with high probability'; the output always has n samples
--   - reading: the algorithm is online and never discards two consecutive samples → the sample retained at step t is x_t if accepted, else y_t; acceptance and the retained sample depend only on s and the inputs of steps ≤ t; reason: the structural properties of the framework (§3.3, p.13)
--   - reading: spends Õ_d(1) time to process each sample → at most N_ℓ = (ℓ + 1)^d functions of Π≤ℓ are nonzero at any point, and a step changes φ only at those; reason: the paper has no machine model; this is its justification (§3.3, p.13)
--   - encoding: f ∈ L²([0,1)^d) with finite σ_SO(f) → a measurable f with MemLp f 2 on the cube and σ_SO(f)² < ∞ in ℝ≥0∞; reason: a measurable representative is needed to evaluate g at sample points; values off the cube are never used
--   - encoding: expectations and ‖g‖²_B as real numbers → lower Lebesgue integrals and sums in ℝ≥0∞; reason: nonnegative quantities; ℝ≥0∞ has no junk value for a divergent sum or a non-integrable integrand
--   - generalization: the algorithm's own randomness (i.i.d. uniform samples and coins) → any probability space carrying a measurable uniform shift and input stream, all mutually independent (IsShiftedStreamInput); reason: the canonical product space is one such space (proved in the sanity file); every statement about the law of the run specializes to it
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), Theorem 1.2, p.2 (PDF p.4), restated p.8 (PDF p.10); algorithm §3.1, pp.8–9 (PDF pp.10–11); proof §3.3, pp.12–13 (PDF pp.14–15)

import Mathlib
import Definitions.Def_QMCBeyondHK_haarRun
import Definitions.Def_QMCBeyondHK_sigmaSOSq
import Definitions.Def_QMCBeyondHK_IsStreamInput

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QMCBeyondHK

/-- Theorem 1.2 (QMC beyond Hardy–Krause via `(1 + ε)n` samples), printed p.2 (PDF p.4; restated
p.8) of Ezeunala, Jha, Jiang, arXiv:2609.10921 (sha256 bc273e88…), for the uniformly-shifted
Haar-thinning algorithm of §3.1 with `ℓ = ⌈10 log₂ n⌉`:
(a) it uses more than `(1 + ε)n` samples with probability at most `exp(−cεn)`;
(b) for every `f ∈ L²([0,1)^d)` with finite `σ_SO(f)`, `E[err(A_s, f)²] ≤ C_d N_ℓ² ε⁻² σ_SO(f)²/n²`;
(c) it is online and never discards two consecutive samples;
(d) each step evaluates a sum of at most `N_ℓ = (ℓ+1)^d` nonzero Haar terms and changes `φ` only at
those Haar functions.

**Formalization Note** `Õ_{d,ε}(σ²_SO(f)/n²)` is pinned as `C_d · N_ℓ² · ε⁻² · σ_SO(f)²/n²`
(`N_ℓ² = O(log n)^{2d}`, footnotes 3–4); `c` is absolute and `C` depends on `d` only, both chosen
before `d, ε, n`. The algorithm reads an unbounded independent uniform stream; the expectation in
(b) is over the whole run (shift, samples and coins), unconditioned, as a lower Lebesgue integral.
"Õ_d(1) time per sample" is the term count of p.13. -/
theorem theorem_1_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℕ → ℝ, ∀ d : ℕ, 1 ≤ d → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ n : ℕ, 1 ≤ n →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (s : Ω → Fin d → ℝ) (X : ℕ → Ω → Fin d → ℝ) (Ξ : ℕ → Ω → ℝ) (Y : ℕ → Ω → Fin d → ℝ),
      IsShiftedStreamInput P s X Ξ Y →
      P {ω | (1 + ε) * (n : ℝ) < (numSamples d ε n (s ω) (X · ω) (Ξ · ω) (Y · ω) : ℝ)}
          ≤ ENNReal.ofReal (Real.exp (-(c * ε * n))) ∧
      (∀ f : (Fin d → ℝ) → ℝ, Measurable f → MemLp f 2 (unif d) → sigmaSOSq d f < ⊤ →
        ∫⁻ ω, ENNReal.ofReal (err (shiftedOutput d ε n (s ω) (X · ω) (Ξ · ω) (Y · ω)) f ^ 2) ∂P
          ≤ ENNReal.ofReal (C d * (Nell d (ell n) : ℝ) ^ 2 / (ε ^ 2 * (n : ℝ) ^ 2)) * sigmaSOSq d f) ∧
      (∀ ω, ∀ t : Fin n,
        (ShiftedAccepts d ε n (s ω) (X · ω) (Ξ · ω) (Y · ω) t →
          shiftedOutput d ε n (s ω) (X · ω) (Ξ · ω) (Y · ω) t = X t ω) ∧
        (¬ ShiftedAccepts d ε n (s ω) (X · ω) (Ξ · ω) (Y · ω) t →
          shiftedOutput d ε n (s ω) (X · ω) (Ξ · ω) (Y · ω) t = Y t ω)) ∧
      (∀ ω ω', ∀ t : Fin n, s ω = s ω' →
        (∀ u : ℕ, u ≤ t → X u ω = X u ω' ∧ Ξ u ω = Ξ u ω' ∧ Y u ω = Y u ω') →
        (ShiftedAccepts d ε n (s ω) (X · ω) (Ξ · ω) (Y · ω) t ↔
          ShiftedAccepts d ε n (s ω') (X · ω') (Ξ · ω') (Y · ω') t) ∧
        shiftedOutput d ε n (s ω) (X · ω) (Ξ · ω) (Y · ω) t
          = shiftedOutput d ε n (s ω') (X · ω') (Ξ · ω') (Y · ω') t) ∧
      (∀ x ∈ cube d, ((lowOrder d (ell n)).filter (fun H => haar H x ≠ 0)).card ≤ Nell d (ell n)) ∧
      (∀ ω, ∀ t : ℕ, ∀ H ∈ lowOrder d (ell n),
        haar H (haarPoint d ε (ell n) (fun u => fracSub (X u ω) (s ω)) (Ξ · ω)
          (fun u => fracSub (Y u ω) (s ω)) t) = 0 →
        disc (shiftedRun d ε n (s ω) (X · ω) (Ξ · ω) (Y · ω) (t + 1)) H
          = disc (shiftedRun d ε n (s ω) (X · ω) (Ξ · ω) (Y · ω) t) H) := by sorry

end QMCBeyondHK
