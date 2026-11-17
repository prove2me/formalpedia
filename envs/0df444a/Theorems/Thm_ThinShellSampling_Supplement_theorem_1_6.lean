-- Prove2me | Theorems.Thm_ThinShellSampling_Supplement_theorem_1_6
-- name    : ThinShellSampling.Supplement.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:40:37.871199+00:00
-- url     : https://prove2.me/theorems/e8e37dd7-e2a7-4ed5-9150-f93d46de40bd
-- title:
--   Theorem 1.6 — $\mathsf{PS}_{\exp}$ with restart: zeroth-order $\mathsf R_q\to\mathsf R_q$ logconcave sampling in $\widetilde O(qn^2\Lambda\log^3(1/\varepsilon))$ queries
-- statement:
--   Let $V:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be convex, given by an evaluation oracle, let $\pi\propto e^{-V}$ be the logconcave distribution it defines, assume $B(0,1)\subseteq\mathsf L_g=\{x:V(x)-\min V\le10n\}$, and let $\Lambda=\|\operatorname{cov}\pi\|_{\mathrm{op}}$. There are universal constants $c_0,C>0$ and $k\in\mathbb N$ with the following property. Let $\varepsilon\in(0,1/100)$, let $\pi_0$ be an initial distribution, and let
--
--   $$
--   q\ \ge\ 2\vee c_0\log\frac{n^2\Lambda}{\varepsilon}\qquad\text{with}\qquad M_q=\Big\|\frac{d\pi_0}{d\pi}\Big\|_{L^q(\pi)}\le10 .
--   $$
--
--   Then there are a step size $h>0$, a threshold $\tau\ge1$ and an iteration count $N\le C\,b_N\log^k(2+b_N)$, $b_N=qn^2\Lambda\log^2(1/\varepsilon)$, such that the algorithm that runs $\mathsf{PS}_{\exp}$ (the proximal sampler on the exponential lift) for $N$ iterations from $\pi_0$ and restarts from scratch whenever a backward step exceeds $\tau$ proposals satisfies:
--
--   1. a single attempt fails (so the algorithm restarts) with probability at most $1/50$;
--   2. the algorithm halts almost surely, and its output $Z$ (the $X$-component) satisfies $\mathsf R_q(\operatorname{law}Z\,\|\,\pi)\le\varepsilon$;
--   3. its expected total number of evaluation queries is at most $C\,b\log^k(2+b)$ with $b=qn^2\Lambda\log^3(1/\varepsilon)$.
--
--   This is the zeroth-order counterpart of Theorem 1.1: with the warm start of Theorem 1.7 it gives an end-to-end logconcave sampler with $\mathsf R_q$ guarantees.
--
--   **Formalization Note** $V$ takes values in `WithTop ℝ` and satisfies the published `IsStandardPotential`; $\pi$ is `piOf V`. $M_q\le10$ is written as $\mathsf R_q(\pi_0\|\pi)\le\frac q{q-1}\log10$; the initial distribution is drawn as $g(u)$ for a measurable $g$ with $g_\#\mathrm{Uniform}[0,1]=\pi_0$.
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
--   - encoding: convex V : ℝⁿ → ℝ ∪ {+∞} given by an evaluation oracle, π ∝ e^{−V}, B(0, 1) ⊂ L_g → V : ℝⁿ → WithTop ℝ with the published IsStandardPotential V (convex, open B(0, 1) ⊆ L_g, ∫ e^{−V} < ∞), π = piOf V; reason: as in the published goal; normalizability is implicit in π ∝ e^{−V}; the open ball is the weaker hypothesis
--   - reading: "runs PS_exp initialized at π₀" → X′ = g(u), one evaluation query of V(X′), T′ = V(X′)/n + E/n with E ∼ Exp(1); the attempt fails if V(X′) = ∞; Z is the X-component; reason: §6.1, p.34 initializes the lifted chain by T′ ∼ π^{T|X=X′} ∝ e^{−nt} on [V(X′)/n, ∞), which needs V(X′); V(X′) < ∞ π₀-a.s. since π₀ ≪ π
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), Theorem 1.6, p.5 (PDF p.7); §6.1, p.34 (PDF p.36); proof p.35 (PDF p.37) via Proposition 6.1, pp.34–35 (PDF pp.36–37)

import Mathlib
import Definitions.Def_ThinShellSampling_renyi
import Definitions.Def_ThinShellSampling_covMat
import Definitions.Def_ThinShellSampling_piOf
import Definitions.Def_ThinShellSampling_Prog
import Definitions.Def_ThinShellSampling_Supplement_restartLaw
import Definitions.Def_ThinShellSampling_Supplement_psExpAttempt

set_option autoImplicit false

namespace ThinShellSampling.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Theorem 1.6 (Zeroth-order logconcave sampling from a warm start).**

Y. Kook, S. S. Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave
Sampling with Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256
25a041a9…), Theorem 1.6, p.5 (PDF p.7): "For a convex function `V : ℝⁿ → ℝ ∪ {+∞}`, given by an
evaluation oracle, let `π ∝ e^{−V}` be the logconcave distribution over `ℝⁿ` with `B(0, 1) ⊂ L_g` and
`Λ = ‖cov π‖_op`. Given `ε ∈ (0, 1/100)`, an initial distribution `π₀`, and `q ≥ 2 ∨ Θ(log(n²Λ/ε))`
such that `M_q = ‖dπ₀/dπ‖_{L^q(π)} ≤ 10`, consider the algorithm that runs `PS_exp` initialized at
`π₀` and restarts if `PS_exp` fails before completing `N = Õ(qn²Λ log² 1/ε)` iterations. There exist
choices of `h` and `τ` such that this algorithm restarts with probability at most `1/50`, and its
output `Z` satisfies `R_q(law Z ‖ π) ≤ ε`, using `Õ(qn²Λ log³ 1/ε)` evaluation queries in
expectation." Proof p.35 (PDF p.37), via Proposition 6.1.

**Formalization Note.**
* **Constants.** `Θ(·)` is a universal `c₀ > 0`, `Õ(b)` is `≤ C·b·log(2 + b)^k` with universal
  `C, k` (§1.3, p.12), all chosen before the instance; `h > 0`, `τ ≥ 1`, `N` per instance.
* **Target.** `V : ℝⁿ → WithTop ℝ` with `IsStandardPotential V` (convex, open `B(0, 1) ⊆ L_g`,
  `∫ e^{−V} < ∞`), `π = piOf V`, as in the published goal.
* **Warmness.** `M_q ≤ 10` is `R_q(π₀ ‖ π) ≤ q/(q − 1)·log 10`; `π₀` is the push-forward of
  `Uniform[0, 1]` under a measurable `g`.
* **Algorithm.** The attempt is `psExpAttempt n h τ N g` on the untruncated exponential lift (its
  initialization `T' ∼ π^{T|X=X'}` costs one evaluation query, each backward proposal one); `Z` is the
  `X`-component of the output of its restart-until-success wrapper. "Restarts with probability at most
  `1/50`" is the probability that one attempt declares failure. -/
theorem theorem_1_6 :
    ∃ c₀ C : ℝ, ∃ k : ℕ, 0 < c₀ ∧ 0 < C ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ V : EuclideanSpace ℝ (Fin n) → WithTop ℝ, IsStandardPotential V →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 100 →
    ∀ (π₀ : Measure (EuclideanSpace ℝ (Fin n))) (g : ℝ → EuclideanSpace ℝ (Fin n)),
      Measurable g → (volume : Measure unitInterval).map (fun u : unitInterval => g (u : ℝ)) = π₀ →
    ∀ q : ℝ,
      max 2 (c₀ * Real.log ((n : ℝ) ^ 2 * Lam (piOf V) / ε)) ≤ q →
      renyi q π₀ (piOf V) ≤ ENNReal.ofReal (q / (q - 1) * Real.log 10) →
    ∃ h : ℝ, 0 < h ∧ ∃ τ N : ℕ, 1 ≤ τ ∧
      (let p := psExpAttempt n h τ N g
       let Λ := Lam (piOf V)
       let bN : ℝ := q * (n : ℝ) ^ 2 * Λ * Real.log (1 / ε) ^ 2
       let b : ℝ := q * (n : ℝ) ^ 2 * Λ * Real.log (1 / ε) ^ 3
       (N : ℝ) ≤ C * bN * Real.log (2 + bN) ^ k ∧
       ThinShellSampling.streamMeasure {ω | Failed V p ω} ≤ 1 / 50 ∧
       (∀ᵐ ws ∂restartMeasure, RestartHalts V p ws) ∧
       AEMeasurable (restartOutput 0 V p) restartMeasure ∧
       AEMeasurable (restartQueries V p) restartMeasure ∧
       renyi q (restartLaw V p) (piOf V) ≤ ENNReal.ofReal ε ∧
       restartExpQueries V p ≤ ENNReal.ofReal (C * b * Real.log (2 + b) ^ k)) := by sorry

end ThinShellSampling.Supplement
