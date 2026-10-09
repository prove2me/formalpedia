-- Prove2me | Theorems.Thm_WassVarReg_Boundary_assumption3_bound
-- name    : WassVarReg.Boundary.assumption3_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:30.729794+00:00
-- url     : https://prove2.me/theorems/4503ede6-a1c0-4b3f-9a7a-5af6114a8486
-- title:
--   Proof of Lemma EC.11, p. ec11 — Assumption 3 gives ρ̄, C > 0 with E_{P_true}[1{d(z, D_f) < ρ}] ≤ Cρ for ρ < ρ̄
-- statement:
--   Let $(\mathcal Z, d)$ be a second-countable metric space with its Borel $\sigma$-algebra, $P_{\rm true}$ a probability measure on it, $\mathcal F$ a set of losses and $\mathcal D_f \subseteq \mathcal Z$ a closed, $P_{\rm true}$-null set attached to each $f \in \mathcal F$. Write $d(z, D) = \inf_{\tilde z \in D} d(z, \tilde z)$ with $d(z, \varnothing) = +\infty$. If Assumption 3 (bounded density) holds, then there exist $\bar\rho > 0$ and $C > 0$ such that for all $0 \le \rho < \bar\rho$ and all $f \in \mathcal F$,
--   $$\mathbb E_{P_{\rm true}}\bigl[\mathbf 1\{d(z, \mathcal D_f) < \rho\}\bigr] \le C\rho.$$
--
--   This is the step of the proof of Lemma EC.11 that converts the bounded-density assumption into a linear bound on the true mass of a $\rho$-neighbourhood of the non-smooth set, uniformly over the class.
--
--   **Formalization Note** The closedness and nullity of $\mathcal D_f$ are Assumption 1's standing requirements ($\mathcal D_f$ is a finite union of closed sets, assumed $P_{\rm true}$-null, p. 6): Assumption 3 controls only the shell $0 < d(z, \mathcal D_f) < \delta$, and an atom on $\mathcal D_f$ would make the left side bounded below for every $\rho$. Second countability is a technical space hypothesis used across this paper's mission series. The radius $\rho$ is nonnegative; for $\mathcal D_f = \varnothing$ the event is empty.
-- source:
--   Gao, Chen & Kleywegt, arXiv:1712.06050 (2020-10-30 version), proof of Lemma EC.11, p. ec11, first sentence after the first display ('By Assumption 3, there exists ρ̄ > 0 …'); Assumption 3, p. 7; Assumption 1, p. 6

import Mathlib
import Definitions.Def_WassVarReg_Boundary_Setting

open MeasureTheory Filter Topology
open scoped ENNReal

namespace WassVarReg.Boundary

/-- Proof of Lemma EC.11, p. ec11: under Assumption 3 there are `ρ̄, C > 0` with
`E_{P_true}[1{d(z, D_f) < ρ}] ≤ Cρ` for all `0 ≤ ρ < ρ̄` and all `f ∈ F`.
`hD`: each `D_f` is closed and `P_true`-null (Assumption 1, p. 6). -/
theorem assumption3_bound {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [SecondCountableTopology Z]
    (Ptrue : ProbabilityMeasure Z) (F : Set (Z → ℝ)) (D : (Z → ℝ) → Set Z)
    (hD : ∀ f ∈ F, IsClosed (D f) ∧ (Ptrue : Measure Z) (D f) = 0)
    (hA3 : Assumption3 Ptrue F D) :
    ∃ ρbar > 0, ∃ C > 0, ∀ ρ : ℝ, 0 ≤ ρ → ρ < ρbar → ∀ f ∈ F,
      ((Ptrue : Measure Z) {z | Metric.infEDist z (D f) < ENNReal.ofReal ρ}).toReal ≤ C * ρ := by sorry

end WassVarReg.Boundary
