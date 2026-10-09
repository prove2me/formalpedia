-- Prove2me | Theorems.Thm_WassVarReg_PInf_exists_optimal_coupling
-- name    : WassVarReg.PInf.exists_optimal_coupling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:09:34.219595+00:00
-- url     : https://prove2.me/theorems/1638a2ef-068e-4e68-93c3-f406e66d4fea
-- title:
--   Proof of Lemma EC.2, p. ec1 — optimal W∞ coupling for finite nominal support
-- statement:
--   Let $Q=\sum_{j=1}^{m}q_j\delta_{z_j}$ be a probability law with finite support, and let $P$ be another probability law on the metric space $Z$. If $\rho\ge0$ and $W_\infty(P,Q)\le\rho$, then there is a coupling $\pi$ of $P$ and $Q$ such that
--   $$
--   \operatorname*{ess\,sup}_{(\tilde z,z)\sim\pi}d(\tilde z,z)\le W_\infty(P,Q).
--   $$
--   Thus the infimum defining $W_\infty(P,Q)$ is attained in the finite-support case. This is the coupling assertion used in the proof of Lemma EC.2.
--
--   **Formalization Note** The metric space has its Borel measurable structure and is second countable so the distance on $Z\times Z$ is measurable. The weights are nonnegative and sum to one.
-- source:
--   Gao, Chen & Kleywegt, arXiv:1712.06050 (2020-10-30 version), proof of Lemma EC.2, p. ec1 (PDF p. 24)

import Mathlib
import Definitions.Def_WassVarReg_PInf_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace WassVarReg.PInf

/-- Proof of Lemma EC.2, p. ec1: finite support of the nominal law ensures an
order-infinity transport distance at most `ρ` is attained by a coupling. -/
theorem exists_optimal_coupling {Z : Type*} [MetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [SecondCountableTopology Z] {m : ℕ}
    (q : Fin m → ℝ≥0) (zs : Fin m → Z) (hq : ∑ j, q j = 1)
    (P : ProbabilityMeasure Z) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hW : winfDist P (discreteLaw q zs hq) ≤ ENNReal.ofReal ρ) :
    ∃ γ : Measure (Z × Z),
      γ ∈ WassersteinLinOpt.Ball.couplings (P : Measure Z)
        (discreteLaw q zs hq : Measure Z) ∧
      essSup (fun x : Z × Z => ENNReal.ofReal (dist x.1 x.2)) γ ≤
        winfDist P (discreteLaw q zs hq) := by sorry

end WassVarReg.PInf
