-- Prove2me | Theorems.Thm_PhysReaudit_Supplement_theorem_18
-- name    : PhysReaudit.Supplement.theorem_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:26:13.508588+00:00
-- url     : https://prove2.me/theorems/38eb182a-8d39-41cb-85b0-f686e5234fc6
-- title:
--   Theorem 18 — adaptive coordinate-sampling lower bound $\sup_\theta\mathbb E_\theta L_A(\hat\theta,\theta)\ge S_A^2/B$
-- statement:
--   Consider the Gaussian coordinate-query model of Appendix D.1. An unknown parameter $\theta\in\mathbb R^d$ is probed one coordinate at a time: a query to coordinate $i$ costs $c_i>0$ and returns
--   $$
--   Y=\theta_i+Z,\qquad Z\sim N(0,1),
--   $$
--   with noise independent across queries. A **predictable coordinate-sampling strategy** chooses each next coordinate, and when to stop, from the past observations and independent randomization; it has **pathwise cost at most $B$** if on every sample path it stops and the total cost of its queries is at most $B$. A **coherent reusable estimator** outputs one vector $\hat\theta$ computed from the complete stopped transcript. For $A=\operatorname{diag}(a_1,\dots,a_d)$ with $a_i>0$ put
--   $$
--   L_A(\hat\theta,\theta)=\|A(\hat\theta-\theta)\|_2^2=\sum_i a_i^2(\hat\theta_i-\theta_i)^2,\qquad S_A=\sum_i a_i\sqrt{c_i}.
--   $$
--
--   **Theorem.** For every coherent reusable estimator and every predictable coordinate-sampling strategy with pathwise cost at most $B>0$,
--   $$
--   \sup_{\theta\in\mathbb R^d}\mathbb E_\theta L_A(\hat\theta,\theta)\ \ge\ \frac{S_A^2}{B}.
--   $$
--
--   Adaptivity does not help: the bound equals the risk $S_A^2/B$ of the optimal fixed design of Proposition 17, so no sequential, randomized allocation of the budget improves on the best fixed allocation in the worst case over an unbounded parameter space.
--
--   Differences from the source:
--
--   - encoding: adaptive coordinate choices and stopping rules depend only on past observations and independent randomization → Strategy d U: a randomization u ∼ ρ on an arbitrary measurable space U, drawn once and independent of the noise, and a decision (u, history) ↦ none (stop) or some i (query i), measurable in (u, observed values) for each list of queried coordinates; reason: randomization drawn once is equivalent to fresh randomization at each step; measurability is needed for the risk to be defined
--   - encoding: Y = θi + Z, Z ∼ N(0, 1), noise variables independent → one i.i.d. gaussianReal 0 1 stream (Z_k)_{k∈ℕ}; the k-th query overall returns θ_{i_k} + Z_k; reason: the coordinate choice is predictable, so each query sees a fresh independent N(0, 1) noise
--   - encoding: pathwise cost at most B → PathwiseBudget: for every θ, u and noise stream the run stops after finitely many decisions with Σ_k c_{i_k} ≤ B; reason: "realized total cost is at most B on every sample path" (App. D.1)
--   - encoding: coherent reusable estimator θ̂; E_θ L_A(θ̂, θ) with L_A = ‖A(θ̂ − θ)‖₂² (9) → Estimator: a measurable map (u, final history) ↦ θ̂ ∈ Fin d → ℝ; risk = ∫⁻ ofReal (Σ_i a_i² (θ̂_i − θ_i)²) under u ∼ ρ and the noise, in ℝ≥0∞; sup over θ : Fin d → ℝ as ⨆ in ℝ≥0∞; reason: the same loss (A diagonal); valuing the risk in [0, ∞] keeps an infinite risk or supremum meaningful
-- source:
--   Q. Li, When Can Physical Evidence Survive a World-Model Update? Finite-cost re-auditing and reusable policy certificates, review revision of 3 November 2026 (STOC 2027 submission, sha256 a20c437b34115b84982339e9a6fa319cb3a66f66d9d4c474465cbb954c79093d), Theorem 18 (Adaptive coordinate-sampling lower bound), p.23 (PDF p.24), display (14); model App. D.1, p.21 (PDF p.22), displays (8)–(9); S_A defined in App. D.3, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_PhysReaudit_Supplement_Strategy
import Definitions.Def_PhysReaudit_Supplement_risk

open MeasureTheory

namespace PhysReaudit.Supplement

/-- **Theorem 18 (Adaptive coordinate-sampling lower bound)** (Q. Li, *When Can Physical Evidence Survive a
World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), Theorem 18, p.23 (PDF p.24),
display (14)).

In the Gaussian coordinate-query model of App. D.1 (a query to coordinate `i` costs `c_i > 0` and returns
`θ_i + Z`, `Z ∼ N(0, 1)` fresh), let `A = diag(a_1, …, a_d)` with `a_i > 0` and `S_A = Σ_i a_i √c_i`. For
every randomized predictable coordinate-sampling strategy `S` (randomization law `ρ`) whose realized total
cost is at most `B > 0` on every sample path, and every coherent reusable estimator `E`,
`sup_{θ ∈ ℝ^d} E_θ L_A(θ̂, θ) ≥ S_A² / B`. -/
theorem theorem_18 {d : ℕ} {U : Type} [MeasurableSpace U] (ρ : Measure U) [IsProbabilityMeasure ρ]
    (a c : Fin d → ℝ) (ha : ∀ i, 0 < a i) (hc : ∀ i, 0 < c i) {B : ℝ} (hB : 0 < B)
    (S : Strategy d U) (hS : PathwiseBudget S c B) (E : Estimator d U) :
    ENNReal.ofReal ((∑ i, a i * Real.sqrt (c i)) ^ 2 / B) ≤ ⨆ θ : Fin d → ℝ, risk ρ S E a θ := by sorry

end PhysReaudit.Supplement
