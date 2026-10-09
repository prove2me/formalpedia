-- Prove2me | Theorems.Thm_WassVarReg_Boundary_lemma_EC_11
-- name    : WassVarReg.Boundary.lemma_EC_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:51.148461+00:00
-- url     : https://prove2.me/theorems/92622e16-f2c8-4946-9947-e2dd8ae690cc
-- title:
--   Lemma EC.11, p. ec11 — w.p. ≥ 1 − e^{−t}, E_{P_n}[1{d(z, D_f) < ρ}] ≤ Cρ + 2E_⊗[ℜ_n(I_ρ)] + √(t/2n) for every f
-- statement:
--   Let $(\mathcal Z, d)$ be a second-countable metric space with its Borel $\sigma$-algebra, $P_{\rm true}$ a probability measure on it, $\mathcal F$ a set of losses and $\mathcal D_f$ a closed, $P_{\rm true}$-null set attached to each $f \in \mathcal F$. Let $\mathcal I_\rho = \{z \mapsto \mathbf 1\{d(z, \mathcal D_f) < \rho\} : f \in \mathcal F,\ \mathcal D_f \ne \varnothing\}$, and let $P_n$ be the empirical law of an i.i.d. sample of size $n \ge 1$ from $P_{\rm true}$. Assume Assumption 3 holds. Then there exist $\bar\rho > 0$ and $C > 0$ such that for all $n \ge 1$, all $t > 0$ and all $0 \le \rho < \bar\rho$, with probability at least $1 - e^{-t}$, for every $f \in \mathcal F$,
--   $$\mathbb E_{P_n}\bigl[\mathbf 1\{d(z, \mathcal D_f) < \rho\}\bigr] \le C\rho + 2\,\mathbb E_\otimes[\mathfrak R_n(\mathcal I_\rho)] + \sqrt{\frac{t}{2n}}.$$
--
--   The lemma bounds the fraction of data points within distance $\rho$ of the non-smooth set of a loss, uniformly over the loss class; multiplied by $\rho$ it gives Theorem 1(III).
--
--   **Formalization Note**
--   1. The page says "Let $t > 0$. Then there exists $\bar\rho, C > 0$"; here $\bar\rho$ and $C$ are chosen before $n$ and $t$. They come from Assumption 3 alone in the proof, so this is the stronger reading and still the proof's content.
--   2. The probability is the product measure of the set of samples on which some $f \in \mathcal F$ violates the bound (outer measure).
--   3. Standing and technical hypotheses: each $\mathcal D_f$ is closed and $P_{\rm true}$-null (Assumption 1, p. 6); the space is second countable; and each class $\mathcal I_\rho$ is Rademacher-measurable at every sample size (measurability of the uniform deviation, the empirical Rademacher complexity and the double-sample deviation; true for countable $\mathcal F$). The latter two are technical hypotheses left implicit by the paper.
--   4. The "Moreover" part of the lemma (Dudley's entropy integral) is not stated: its proof bounds the empirical Rademacher complexity at the observed sample, whereas Lemma EC.5 needs its expectation.
-- source:
--   Gao, Chen & Kleywegt, arXiv:1712.06050 (2020-10-30 version), Lemma EC.11, first inequality, p. ec11

import Mathlib
import Definitions.Def_WassVarReg_Boundary_Setting

open MeasureTheory Filter Topology
open scoped ENNReal

namespace WassVarReg.Boundary

/-- Lemma EC.11, first inequality, p. ec11. `hD`: each `D_f` is closed and `P_true`-null
(Assumption 1, p. 6); `hguard`: measurability guard for the classes `I_ρ`. -/
theorem lemma_EC_11 {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [SecondCountableTopology Z]
    (Ptrue : ProbabilityMeasure Z) (F : Set (Z → ℝ)) (D : (Z → ℝ) → Set Z)
    (hD : ∀ f ∈ F, IsClosed (D f) ∧ (Ptrue : Measure Z) (D f) = 0)
    (hguard : ∀ (n : ℕ) (ρ : ℝ), RademacherMeasurable n Ptrue (indicatorClass ρ F D))
    (hA3 : Assumption3 Ptrue F D) :
    ∃ ρbar > 0, ∃ C > 0, ∀ n : ℕ, 0 < n → ∀ t : ℝ, 0 < t → ∀ ρ : ℝ, 0 ≤ ρ → ρ < ρbar →
      MinimaxWass.DataDep.sampleLaw n Ptrue
        {ω | ¬ ∀ f ∈ F, (1 / (n : ℝ)) * ∑ i : Fin n, nearIndicator ρ (D f) (ω i) ≤
          C * ρ + 2 * rademacher n Ptrue (indicatorClass ρ F D) + Real.sqrt (t / (2 * n))} ≤
        ENNReal.ofReal (Real.exp (-t)) := by sorry

end WassVarReg.Boundary
