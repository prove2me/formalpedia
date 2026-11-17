-- Prove2me | Theorems.Thm_ThinShellSampling_Supplement_theorem_1_1
-- name    : ThinShellSampling.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:39:16.155205+00:00
-- url     : https://prove2.me/theorems/4018ec37-6904-45d6-9b63-a206dada624c
-- title:
--   Theorem 1.1 — $\mathsf{PS}_{\mathrm{unif}}$ with restart: $\mathsf R_q\to\mathsf R_q$ uniform sampling from an $M_q\le10$ warm start in $\widetilde O(qn^2\Lambda\log^6(1/\varepsilon))$ queries
-- statement:
--   Let $\mathcal K\subset\mathbb R^n$ be a convex body (compact and convex) containing the unit ball $B(0,1)$, given by a membership oracle, let $\pi$ be the uniform distribution on $\mathcal K$, and let $\Lambda=\|\operatorname{cov}\pi\|_{\mathrm{op}}$. There are universal constants $c_0,C>0$ and $k\in\mathbb N$ with the following property. Let $\varepsilon\in(0,1/100)$, let $\pi_0$ be an initial distribution, and let
--
--   $$
--   q\ \ge\ 2\vee c_0\log\frac{n^2\Lambda}{\varepsilon}\qquad\text{with}\qquad M_q=\Big\|\frac{d\pi_0}{d\pi}\Big\|_{L^q(\pi)}\le10 .
--   $$
--
--   Then there are a step size $h>0$, a threshold $\tau\ge1$ and an iteration count $N\le C\,b_N\log^k(2+b_N)$, $b_N=qn^2\Lambda\log^2(1/\varepsilon)$, such that the algorithm that runs $\mathsf{PS}_{\mathrm{unif}}$ for $N$ iterations from $\pi_0$ and restarts from scratch whenever a backward step exceeds $\tau$ trials satisfies:
--
--   1. a single attempt fails (so the algorithm restarts) with probability at most $1/50$;
--   2. the algorithm halts almost surely, and its output $Z$ satisfies $\mathsf R_q(\operatorname{law}Z\,\|\,\pi)\le\varepsilon$;
--   3. its expected total number of membership queries is at most $C\,b\log^k(2+b)$ with $b=qn^2\Lambda\log^6(1/\varepsilon)$.
--
--   This is the balanced warm-start guarantee $\mathsf R_q\to\mathsf R_q$ for uniform sampling: an $O(1)$-warm start in $\mathsf R_q$ yields an $\varepsilon$-accurate output in the same order $q$, which combines with the warm start of Theorem 1.5 into an end-to-end sampler.
--
--   **Formalization Note** The membership oracle is the evaluation oracle of the indicator potential, $\pi$ is `piOf (indicatorPot K)`, and $M_q\le10$ is written as $\mathsf R_q(\pi_0\|\pi)\le\frac q{q-1}\log10$. The initial distribution is drawn as $g(u)$ for a uniform $u$ and a measurable $g$ with $g_\#\mathrm{Uniform}[0,1]=\pi_0$.
--
--   Differences from the source:
--
--   - reading: q ≥ 2 ∨ Θ(log(n²Λ/ε)) → max 2 (c₀·log(n²Λ/ε)) ≤ q for a universal c₀ > 0 chosen before the instance; reason: §1.3, p.12: Θ(·) hides a universal constant, which the theorem chooses
--   - reading: N = Õ(qn²Λ log² 1/ε) and Õ(…) queries → ≤ C·b·log(2 + b)^k with universal C > 0, k ∈ ℕ chosen before the instance; reason: §1.3, p.12: a = Õ(b) means a = O(b polylog b); 2 + b keeps the logarithm positive
--   - reading: "There exist choices of h and τ" for N = Õ(qn²Λ log² 1/ε) iterations → ∃ h > 0, τ ≥ 1 and N per instance, with N ≤ C·b_N·log(2 + b_N)^k as a conclusion; reason: the proof chooses h, τ, N from n, Λ, ε and M_q (Proposition 2.8 / 6.1); τ = 0 and h ≤ 0 are not choices of the algorithm
--   - reading: "this algorithm restarts with probability at most 1/50" → the probability that one attempt declares failure is at most 1/50; reason: a restart happens exactly when an attempt fails; the restart run itself fails with probability 0
--   - reading: "its output Z satisfies R_q(law Z ∥ π) ≤ ε, using … in expectation" → the restart run halts almost surely, its output map and total query count are a.e.-measurable, renyi q (law Z) π ≤ ε and the expected total query count is bounded; reason: law Z exists only for an a.s.-halting run with a measurable output
--   - encoding: an initial distribution π₀ → π₀ = push-forward of Uniform[0, 1] under a measurable g : ℝ → ℝⁿ, drawn by the program at no query cost; reason: every Borel probability measure on ℝⁿ (a standard Borel space) is such a push-forward, so no instance is lost
--   - encoding: M_q = ∥dπ₀/dπ∥_{L^q(π)} ≤ 10 → renyi q π₀ π ≤ ofReal(q/(q − 1)·log 10); reason: R_q = q/(q − 1)·log M_q by (1.2) for q > 1; renyi is ∞ exactly when π₀ is not ≪ π, where M_q = ∞
--   - encoding: restart from scratch with a new x₀ ∼ π₀ after a failure → restart-until-success wrapper (restartLaw, restartExpQueries) over independent uniform streams, number of restarts uncapped; reason: a Prog has only finite run paths, so the unbounded loop is defined on top of the attempt; same algorithm
--   - encoding: Gaussian draws N(·, h I) → Box–Muller from the uniform stream (published gaussVec, stdNormal), no query cost; reason: same law; only oracle calls are charged in the paper
--   - encoding: convex body K ⊂ ℝⁿ given by a membership oracle with B(0, 1) ⊂ K; π uniform on K → K compact and convex with the open unit ball ⊆ K; the oracle is the evaluation oracle of indicatorPot K; π = piOf (indicatorPot K); reason: a query answers x ∈ K; for closed K the open and closed unit-ball readings agree
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), Theorem 1.1, p.3 (PDF p.5); proof pp.18–19 (PDF pp.20–21) via Proposition 2.8, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_ThinShellSampling_renyi
import Definitions.Def_ThinShellSampling_covMat
import Definitions.Def_ThinShellSampling_piOf
import Definitions.Def_ThinShellSampling_Prog
import Definitions.Def_ThinShellSampling_Supplement_restartLaw
import Definitions.Def_ThinShellSampling_Supplement_indicatorPot
import Definitions.Def_ThinShellSampling_Supplement_psUnifAttempt

set_option autoImplicit false

namespace ThinShellSampling.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Theorem 1.1 (Uniform sampling from a warm start).**

Y. Kook, S. S. Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave
Sampling with Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256
25a041a9…), Theorem 1.1, p.3 (PDF p.5): "Let `π` be the uniform distribution over a convex body
`K ⊂ ℝⁿ` given by a membership oracle with `B(0, 1) ⊂ K` and `Λ = ‖cov π‖_op`. Given
`ε ∈ (0, 1/100)`, an initial distribution `π₀`, and `q ≥ 2 ∨ Θ(log(n²Λ/ε))` such that
`M_q = ‖dπ₀/dπ‖_{L^q(π)} ≤ 10`, consider the algorithm that runs `PS_unif` initialized at `π₀` and
restarts if `PS_unif` fails before completing `N = Õ(qn²Λ log² 1/ε)` iterations. There exist choices
of `h` and `τ` such that this algorithm restarts with probability at most `1/50`, and its output `Z`
satisfies `R_q(law Z ‖ π) ≤ ε`, using `Õ(qn²Λ log⁶ 1/ε)` total membership queries in expectation."
Proof pp.18–19 (PDF pp.20–21), via Proposition 2.8.

**Formalization Note.**
* **Constants.** `Θ(·)` in the hypothesis on `q` is a universal `c₀ > 0` and `Õ(b)` is
  `≤ C·b·log(2 + b)^k` with universal `C, k` (§1.3, p.12); `c₀, C, k` are chosen before every
  instance. `h > 0`, `τ ≥ 1` and `N` are chosen per instance ("there exist choices"), with the bound
  on `N` a conclusion.
* **Target.** `π = piOf (indicatorPot K)`, the uniform distribution on `K`; the membership oracle is
  the evaluation oracle of the indicator potential. A convex body is a compact convex set; `B(0, 1)`
  is the open ball (for compact `K` the two readings agree).
* **Warmness.** `M_q ≤ 10` is `R_q(π₀ ‖ π) ≤ q/(q − 1)·log 10` (eq. (1.2): `R_q = q/(q−1)·log M_q`);
  `renyi` is `∞` off absolute continuity, so this also gives `π₀ ≪ π`. `π₀` is the push-forward of
  `Uniform[0, 1]` under a measurable `g` (every Borel probability measure on `ℝⁿ` is such a law).
* **Algorithm.** The attempt is `psUnifAttempt n h τ N g`; the algorithm is its restart-until-success
  wrapper (`restartLaw`, `restartExpQueries`). "Restarts with probability at most `1/50`" is the
  probability that one attempt declares failure. -/
theorem theorem_1_1 :
    ∃ c₀ C : ℝ, ∃ k : ℕ, 0 < c₀ ∧ 0 < C ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ K : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact K → Convex ℝ K → Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 100 →
    ∀ (π₀ : Measure (EuclideanSpace ℝ (Fin n))) (g : ℝ → EuclideanSpace ℝ (Fin n)),
      Measurable g → (volume : Measure unitInterval).map (fun u : unitInterval => g (u : ℝ)) = π₀ →
    ∀ q : ℝ,
      max 2 (c₀ * Real.log ((n : ℝ) ^ 2 * Lam (piOf (indicatorPot K)) / ε)) ≤ q →
      renyi q π₀ (piOf (indicatorPot K)) ≤ ENNReal.ofReal (q / (q - 1) * Real.log 10) →
    ∃ h : ℝ, 0 < h ∧ ∃ τ N : ℕ, 1 ≤ τ ∧
      (let V := indicatorPot K
       let p := psUnifAttempt n h τ N g
       let Λ := Lam (piOf V)
       let bN : ℝ := q * (n : ℝ) ^ 2 * Λ * Real.log (1 / ε) ^ 2
       let b : ℝ := q * (n : ℝ) ^ 2 * Λ * Real.log (1 / ε) ^ 6
       (N : ℝ) ≤ C * bN * Real.log (2 + bN) ^ k ∧
       ThinShellSampling.streamMeasure {ω | Failed V p ω} ≤ 1 / 50 ∧
       (∀ᵐ ws ∂restartMeasure, RestartHalts V p ws) ∧
       AEMeasurable (restartOutput 0 V p) restartMeasure ∧
       AEMeasurable (restartQueries V p) restartMeasure ∧
       renyi q (restartLaw V p) (piOf V) ≤ ENNReal.ofReal ε ∧
       restartExpQueries V p ≤ ENNReal.ofReal (C * b * Real.log (2 + b) ^ k)) := by sorry

end ThinShellSampling.Supplement
