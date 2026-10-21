-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P01_classicalRigidityObstruction
-- name    : QAlgorithms.Papers.Independent.Next46.P01.classicalRigidityObstruction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:32:28.597047+00:00
-- url     : https://prove2.me/theorems/4491fc2b-0b78-4f1b-91b5-20136cb627f8
-- title:
--   Classical finite-time law rigidity forces equilibrium
-- statement:
--   Let $X$ be a compact metric space, $\phi$ a jointly continuous real flow by homeomorphisms, and $\omega$ a Borel probability satisfying (Cl1)–(Cl3). For this implication allow $\omega$ to be invariant. Let $c^t$, $\sigma$, and $Q_{\nu,t}=(c^t)_*\nu$ be its classical entropy cocycle, production observable, and laws. If
--   $$
--   Q_{\omega_T,t}=Q_{\omega,t}\qquad(t,T\ge0),
--   $$
--   then $\omega_t=\omega$ for every real $t$. Consequently, for all real $t$,
--   $$
--   c^t=0\quad\omega\text{-almost everywhere},\qquad
--   \operatorname{Ent}(\omega_t\mid\omega)=0,\qquad Q_{\omega,t}=\delta_0,
--   $$
--   and $\sigma=0$ almost everywhere. Thus the proposed rigidity is incompatible with the non-invariant reference stipulated in Section 2.6. Stating the implication in the ambient regular system preserves this obstruction without making its hypotheses vacuous.
-- source:
--   Entropic Fluctuations in Statistical Mechanics II. Quantum Dynamical Systems, arXiv:2409.15485v2, PDF p. 28, classical-rigidity-obstruction

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P01

noncomputable section

open Filter MeasureTheory Set

open scoped BigOperators ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P01

section Classical

variable (X : Type*) [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

variable {X}

/-- Classical rigidity obstruction: arXiv:2409.15485v2, PDF p.28, Remark 1.
The ambient implication intentionally allows an invariant reference; in the
source's non-invariant setting its hypothesis is consequently impossible. -/
theorem classicalRigidityObstruction (D : RegularClassicalSystem X)
    (hrigid : ∀ (t T : ℝ), 0 ≤ t → 0 ≤ T →
      classicalLaw D (classicalEvolved D.toClassicalFlowSystem (D.omega : Measure X) T) t =
        classicalLaw D (D.omega : Measure X) t) :
    (∀ t : ℝ, classicalEvolved D.toClassicalFlowSystem (D.omega : Measure X) t =
      (D.omega : Measure X)) ∧
    (∀ t : ℝ,
      ((fun x => D.continuousCocycle t x) =ᵐ[(D.omega : Measure X)] fun _ => 0) ∧
      classicalRelativeEntropy (classicalEvolved D.toClassicalFlowSystem (D.omega : Measure X) t)
        (D.omega : Measure X) = 0 ∧
      classicalLaw D (D.omega : Measure X) t = Measure.dirac 0) ∧
    ((fun x => classicalProduction D x) =ᵐ[(D.omega : Measure X)] fun _ => 0) := by sorry

end Classical

end QAlgorithms.Papers.Independent.Next46.P01

end
