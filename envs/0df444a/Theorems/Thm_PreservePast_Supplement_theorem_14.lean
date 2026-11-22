-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_14
-- name    : PreservePast.Supplement.theorem_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:38:31.315048+00:00
-- url     : https://prove2.me/theorems/a88f7e6b-83df-451a-9370-f73bed7f75b2
-- title:
--   Theorem 14 — Gaussian critical-window memory law
-- statement:
--   In the Gaussian nearest-of-$k$ experiment ($X_j\sim N(0,I_d)$ independent, $Z=\rho X_J+\sqrt{1-\rho^2}\,G$), with costs $I_{\rm tot}=I(X;M\mid R)$, $I_{\rm exc}=I(X;M\mid\Theta,R)$ and fixed width $B$, all in bits, let $k\to\infty$, $d\ge k^{1/10}$ and
--   $$\rho^2d=2\ln k+\tau_k\sqrt{\ln k},\qquad|\tau_k|\le T<\infty,\qquad u_k=\Phi\big(\tau_k/(2\sqrt2)\big).$$
--
--   1. Uniformly in these parameters, $S^\ast=u_k+o(1)$, and every joint protocol of success $S$ satisfies, for $C\in\{I_{\rm tot},I_{\rm exc},B\}$,
--   $$C\ \ge\ \Big(\frac{S}{4u_k}-e_k\Big)kd\log_2\ln k,\qquad e_k\to0 .$$
--   2. If $\tau_k\to\tau$, put $u=\Phi(\tau/(2\sqrt2))$. For each fixed $0<S<u$, all three costs have the matching optimum
--   $$\inf_{\Pr\{\hat J=J\}\ge S}C=\Big(\frac{S}{4u}+o(1)\Big)kd\log_2\ln k .$$
--   3. Every sequence with success $S^\ast-o(1)$ has leading cost at least $(\tfrac14-o(1))kd\log_2\ln k$, and a finite-width sequence attains it.
--
--   **Formalization Note** The experiment and the three costs are those of `PreservePast.Supplement.gaussShift`.
--
--   Differences from the source:
--   - encoding: uniformly in these parameters, o(1) and e_k → 0 → a sequence e_k → 0 chosen after T, valid for all admissible (d, ρ, τ) and all protocols at each k ≥ 3; reason: spells out the uniformity; k ≥ 3 makes log₂ ln k positive
--   - encoding: 0 < ρ < 1 is not repeated in the theorem → the hypothesis 0 < ρ < 1; reason: the standing range of the nearest-of-k experiment (§4.1) and of the hidden-centre representation
--   - encoding: inf over protocols of success ≥ S of each cost equals (S/(4u) + o(1)) kd log₂ ln k, for τ_k → τ → parameters d_k, ρ_k, τ_k as functions of k with τ_k → τ; every protocol of success ≥ S has each cost ≥ (S/(4u) − e_k)kd log₂ ln k, and from some k on one protocol of success ≥ S has all three costs ≤ (S/(4u) + e_k)kd log₂ ln k; reason: two-part form of a least cost; avoids junk values of infima
--   - reading: Every sequence with success S* − o(1) has leading cost at least (1/4 − o(1))kd log₂ ln k, and a finite-width sequence attains it → uniformly over all admissible parameters (no convergence of τ_k): for every ε_k → 0 an e_k → 0 with all three costs ≥ (1/4 − e_k)kd log₂ ln k for protocols of success ≥ S* − ε_k, and an e_k → 0 with a finite-width protocol of success ≥ S* − e_k and width ≤ (1/4 + e_k)kd log₂ ln k; reason: the sentence does not say whether τ_k → τ is still assumed; the uniform form implies the form along every sequence
--   - encoding: S* is the optimal success when the decoder also has the full X → the supremum of the success of jointly measurable decoders of (X, Z); reason: randomizing the decoder cannot increase the optimum
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 14, p.52 (PDF p.54), eqs. (168)–(170); Appendix J, p.52

import Mathlib
import Definitions.Def_PreservePast_Supplement_IdProtocol
import Definitions.Def_PreservePast_Supplement_gaussShift

open MeasureTheory Filter Topology

namespace PreservePast.Supplement

/-- **Theorem 14 (Gaussian critical-window memory law).** P. Xu, *Information Required to Preserve
Past Learning*, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), Theorem 14, p.52
(PDF p.54), eqs. (168)–(170); the experiment is that of Appendix J, p.52.

Let `k → ∞`, `d ≥ k^{1/10}`, `ρ²d = 2 ln k + τ_k√(ln k)`, `|τ_k| ≤ T`, `u_k = Φ(τ_k/(2√2))`.
Uniformly in these parameters `S* = u_k + o(1)`, and every joint protocol of success `S` has
`C ≥ (S/(4u_k) − e_k) kd log₂ ln k`, `e_k → 0`, for `C ∈ {I_tot, I_exc, B}` (169). If `τ_k → τ`
and `u = Φ(τ/(2√2))`, then for each fixed `0 < S < u` all three costs have the optimum
`inf_{Pr{Ĵ=J}≥S} C = (S/(4u) + o(1)) kd log₂ ln k` (170). Every sequence with success
`S* − o(1)` has leading cost at least `(1/4 − o(1)) kd log₂ ln k`, and a finite-width sequence
attains it.

**Formalization Note.** `0 < ρ < 1` (the standing range of the nearest-of-k experiment, §4.1,
p.10). "Uniformly … `o(1)`" is a sequence `e_k → 0`, chosen after `T` only, valid for all
admissible `(d, ρ, τ)` and all protocols at each `k ≥ 3` (so that `log₂ ln k > 0`). The first
block is `S* = u_k + o(1)` and (169). The second block is (170) for parameters
`d_k, ρ_k, τ_k` given as functions of `k` with `τ_k → τ`: for each cost, the lower bound for
every protocol of success `≥ S`, and, from some `k` on, one protocol of success `≥ S` whose
width, total information and sample-specific information are all at most
`(S/(4u) + e_k) kd log₂ ln k`. The third block is the last sentence: for every `ε_k → 0`
there is `e_k → 0` such that protocols of success `≥ S* − ε_k` have all three costs
`≥ (1/4 − e_k) kd log₂ ln k`; and there is `e_k → 0` and, for all admissible parameters, a
finite-width protocol of success `≥ S* − e_k` and width `≤ (1/4 + e_k) kd log₂ ln k`.
Information is an extended nonnegative real, compared through `ENNReal.ofReal`. -/
theorem theorem_14 :
    (∀ T : ℝ, ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ (k d : ℕ) (ρ τ : ℝ), 3 ≤ k → (k : ℝ) ^ ((1 : ℝ) / 10) ≤ d → 0 < ρ → ρ < 1 → |τ| ≤ T →
        ρ ^ 2 * d = 2 * Real.log k + τ * Real.sqrt (Real.log k) →
        |gaussIdOptimum k d ρ - stdNormalCdf (τ / (2 * Real.sqrt 2))| ≤ e k ∧
        ∀ π : StateProtocol (Fin k → Fin d → ℝ) (Fin d → ℝ) (Fin k),
          ENNReal.ofReal ((gaussIdSuccess π ρ / (4 * stdNormalCdf (τ / (2 * Real.sqrt 2))) - e k) *
              (k * d * Real.logb 2 (Real.log k))) ≤ gaussIdTot π ∧
          ENNReal.ofReal ((gaussIdSuccess π ρ / (4 * stdNormalCdf (τ / (2 * Real.sqrt 2))) - e k) *
              (k * d * Real.logb 2 (Real.log k))) ≤ gaussIdExc π ρ ∧
          ∀ B : ℕ, π.HasWidth B →
            (gaussIdSuccess π ρ / (4 * stdNormalCdf (τ / (2 * Real.sqrt 2))) - e k) *
              (k * d * Real.logb 2 (Real.log k)) ≤ (B : ℝ)) ∧
    (∀ (T τ₀ : ℝ) (d : ℕ → ℕ) (ρ τ : ℕ → ℝ),
      (∀ k : ℕ, 3 ≤ k → (k : ℝ) ^ ((1 : ℝ) / 10) ≤ d k ∧ 0 < ρ k ∧ ρ k < 1 ∧ |τ k| ≤ T ∧
        ρ k ^ 2 * d k = 2 * Real.log k + τ k * Real.sqrt (Real.log k)) →
      Tendsto τ atTop (𝓝 τ₀) →
      ∀ S : ℝ, 0 < S → S < stdNormalCdf (τ₀ / (2 * Real.sqrt 2)) →
        ∃ (e : ℕ → ℝ) (k₀ : ℕ), Tendsto e atTop (𝓝 0) ∧ ∀ k : ℕ, k₀ ≤ k → 3 ≤ k →
          (∀ π : StateProtocol (Fin k → Fin (d k) → ℝ) (Fin (d k) → ℝ) (Fin k),
            S ≤ gaussIdSuccess π (ρ k) →
            ENNReal.ofReal ((S / (4 * stdNormalCdf (τ₀ / (2 * Real.sqrt 2))) - e k) *
                (k * d k * Real.logb 2 (Real.log k))) ≤ gaussIdTot π ∧
            ENNReal.ofReal ((S / (4 * stdNormalCdf (τ₀ / (2 * Real.sqrt 2))) - e k) *
                (k * d k * Real.logb 2 (Real.log k))) ≤ gaussIdExc π (ρ k) ∧
            ∀ B : ℕ, π.HasWidth B →
              (S / (4 * stdNormalCdf (τ₀ / (2 * Real.sqrt 2))) - e k) *
                (k * d k * Real.logb 2 (Real.log k)) ≤ (B : ℝ)) ∧
          ∃ (π : StateProtocol (Fin k → Fin (d k) → ℝ) (Fin (d k) → ℝ) (Fin k)) (B : ℕ),
            π.HasWidth B ∧ S ≤ gaussIdSuccess π (ρ k) ∧
            (B : ℝ) ≤ (S / (4 * stdNormalCdf (τ₀ / (2 * Real.sqrt 2))) + e k) *
              (k * d k * Real.logb 2 (Real.log k)) ∧
            gaussIdTot π ≤ ENNReal.ofReal ((S / (4 * stdNormalCdf (τ₀ / (2 * Real.sqrt 2))) + e k) *
              (k * d k * Real.logb 2 (Real.log k))) ∧
            gaussIdExc π (ρ k) ≤
              ENNReal.ofReal ((S / (4 * stdNormalCdf (τ₀ / (2 * Real.sqrt 2))) + e k) *
                (k * d k * Real.logb 2 (Real.log k)))) ∧
    ∀ T : ℝ,
      (∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) → ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
        ∀ (k d : ℕ) (ρ τ : ℝ), 3 ≤ k → (k : ℝ) ^ ((1 : ℝ) / 10) ≤ d → 0 < ρ → ρ < 1 → |τ| ≤ T →
          ρ ^ 2 * d = 2 * Real.log k + τ * Real.sqrt (Real.log k) →
          ∀ π : StateProtocol (Fin k → Fin d → ℝ) (Fin d → ℝ) (Fin k),
            gaussIdOptimum k d ρ - ε k ≤ gaussIdSuccess π ρ →
            ENNReal.ofReal ((1 / 4 - e k) * (k * d * Real.logb 2 (Real.log k))) ≤ gaussIdTot π ∧
            ENNReal.ofReal ((1 / 4 - e k) * (k * d * Real.logb 2 (Real.log k))) ≤
              gaussIdExc π ρ ∧
            ∀ B : ℕ, π.HasWidth B →
              (1 / 4 - e k) * (k * d * Real.logb 2 (Real.log k)) ≤ (B : ℝ)) ∧
      ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
        ∀ (k d : ℕ) (ρ τ : ℝ), 3 ≤ k → (k : ℝ) ^ ((1 : ℝ) / 10) ≤ d → 0 < ρ → ρ < 1 → |τ| ≤ T →
          ρ ^ 2 * d = 2 * Real.log k + τ * Real.sqrt (Real.log k) →
          ∃ (π : StateProtocol (Fin k → Fin d → ℝ) (Fin d → ℝ) (Fin k)) (B : ℕ),
            π.HasWidth B ∧ gaussIdOptimum k d ρ - e k ≤ gaussIdSuccess π ρ ∧
            (B : ℝ) ≤ (1 / 4 + e k) * (k * d * Real.logb 2 (Real.log k)) := by sorry

end PreservePast.Supplement
