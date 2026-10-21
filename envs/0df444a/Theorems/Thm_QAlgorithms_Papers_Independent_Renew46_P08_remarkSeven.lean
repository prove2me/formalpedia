-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_remarkSeven
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.remarkSeven
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:01:58.695413+00:00
-- url     : https://prove2.me/theorems/851a2d84-fdf3-4f4f-ae68-34f9dbe46158
-- title:
--   Remark 7: failure of the Shannon criterion under Dstar
-- statement:
--   Let $p^n$ be countable probability laws converging in $\ell^1$ to the point mass at label zero, with $S(p^n)\to C>0$ finite. Choose any probability law $p^0$ with $S(p^0)=C$ and mutually orthogonal pure states $\rho_i$ on an infinite-dimensional separable system. Construct $\mu_n=\{p_i^n,\rho_i\}$ and $\mu_0=\{p_i^0,\rho_0\}$, so every limit signal is the same state. Then
--
--   $$D_*(\mu_n,\mu_0)\to0,\qquad S(p^n)\to S(p^0)=C,\qquad \chi(\mu_n)=S(p^n)\to C,\quad \chi(\mu_0)=0.$$
--
--   Consequently chi fails to converge to its limit-presentation value, and the presentations do not converge in $D_0$. This is the source's explicit counterexample to using $D_*$ in Proposition 6B's Shannon criterion; desired information values are conclusions of the construction.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 27, Remark 7: failure of the Shannon criterion under Dstar

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P08

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Renew46.P08

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (CountableStateEnsemble convexOperatorMixture)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity traceSize tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats
    extendedRelativeEntropyNats ensembleHolevo)

open QAlgorithms.Papers.Independent.Frontier18.P08
  (partialTraceFirst partialTraceSecond operatorTrace)

open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel)

open QAlgorithms.Papers.Independent.Claimed50.P07
  (boundedCoefficients oscillatorGround oscillatorLevels oscillatorEnvelope oscillatorEntropyBounded)

open QAlgorithms.Papers.Independent.Next46.P08 (continuityRatio MajorantRegularity)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Remark 7, PDF p.27: the source's actual counterexample construction,
for every specified family of laws and orthogonal pure signals satisfying its
data. Desired Holevo values are conclusions, never premises. -/
theorem remarkSeven {I : Type} [Countable I] [Infinite I]
    (p : ℕ → ℕ → ℝ≥0∞) (hp : ∀ n, (∑' i, p n i) = 1)
    (p0 : ℕ → ℝ≥0∞) (hp0 : (∑' i, p0 i) = 1)
    (C : ℝ) (hC : 0 < C)
    (hdegenerate : Tendsto (fun n => ∑' i, |(p n i).toReal -
      (if i = 0 then (1 : ℝ) else 0)|) atTop (nhds 0))
    (hS : Tendsto (fun n => countableShannonNats (p n)) atTop (nhds (ENNReal.ofReal C)))
    (hS0 : countableShannonNats p0 = ENNReal.ofReal C)
    (rho : ℕ → State I)
    (horth : ∃ u : ℕ → Hilbert I, Orthonormal ℂ u ∧
      ∀ i, (rho i).coefficients = QAlgorithms.Papers.Independent.Dependency50.P33.rankOne (u i)) :
    let mu : ℕ → CountableStateEnsemble I := fun n => ⟨p n, hp n, rho⟩
    let mu0 : CountableStateEnsemble I := ⟨p0, hp0, fun _ => rho 0⟩
    Tendsto (fun n => distanceStar (mu n) mu0) atTop (nhds 0) ∧
    Tendsto (fun n => countableShannonNats (mu n).weight) atTop (nhds (countableShannonNats mu0.weight)) ∧
    (∀ n, countableHolevo (mu n) = countableShannonNats (p n)) ∧ countableHolevo mu0 = 0 ∧
    Tendsto (fun n => countableHolevo (mu n)) atTop (nhds (ENNReal.ofReal C)) ∧
    ¬ Tendsto (fun n => countableHolevo (mu n)) atTop (nhds (countableHolevo mu0)) ∧
    ¬ Tendsto (fun n => distance0 (mu n) mu0) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
