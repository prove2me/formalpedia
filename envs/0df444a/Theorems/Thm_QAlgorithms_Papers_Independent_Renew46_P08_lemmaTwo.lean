-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_lemmaTwo
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.lemmaTwo
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:05:49.093844+00:00
-- url     : https://prove2.me/theorems/bd8d220a-7ac3-44b6-84e1-0c83dd1fad97
-- title:
--   Lemma 2, (71)–(72): qc postselection information bounds
-- statement:
--   Let $\rho_{AB}$ be a qc state with finite $H(\rho_A)$, and let $P_A$ be any bounded orthogonal projector. Put $Y=(P_A\otimes I)\rho(P_A\otimes I)$ and $\tau=\operatorname{Tr}Y$. Homogeneous QMI and entropy obey
--
--   $$0\le I(A:B)_\rho-I(A:B)_Y\le H(\rho_A)-H(Y_A).$$
--
--   For $\tau>0$, the normalized state $\widetilde\rho=Y/\tau$ has finite relevant quantities, and
--
--   $$-(1-\tau)H(\widetilde\rho_A)\le I(A:B)_\rho-I(A:B)_{\widetilde\rho}\le H(\rho_A)-\tau H(\widetilde\rho_A).$$
--
--   At $\tau=0$ the homogeneous output quantities are zero. Thus both (71) and (72) are retained, including the zero projector without pretending its normalized output is a state.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 29, Lemma 2, (71)–(72): qc postselection information bounds

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

/-- Lemma 2, PDF pp.29–30, (71)–(72): actual bounded-projector postselection
of a qc state. The homogeneous inequalities include P=0; the normalized (71)
is stated only when its probability is positive. Neither is replaced by the other. -/
theorem lemmaTwo {I : Type} [Countable I] [Nonempty I]
    (mu : CountableStateEnsemble I) (hH : extendedEntropyNats (countableAverage mu) < ⊤)
    (P : Hilbert I →L[ℂ] Hilbert I) (hself : P.adjoint = P) (hproj : P.comp P = P) :
    let X := qcState mu
    let Y := tensorApply (conjugateKernel (boundedCoefficients P)) X
    let tau := operatorTrace Y
    qmi X < ⊤ ∧ homogeneousQmi Y < ⊤ ∧
    extendedEntropyNats (partialTraceSecond Y) < ⊤ ∧
    0 ≤ (qmi X).toReal - (homogeneousQmi Y).toReal ∧
    (qmi X).toReal - (homogeneousQmi Y).toReal ≤
      (extendedEntropyNats (countableAverage mu)).toReal -
        (extendedEntropyNats (partialTraceSecond Y)).toReal ∧
    (tau = 0 → homogeneousQmi Y = 0 ∧ extendedEntropyNats (partialTraceSecond Y) = 0) ∧
    (0 < tau → let Z := ((tau : ℂ)⁻¹) • Y
      qmi Z < ⊤ ∧ extendedEntropyNats (partialTraceSecond Z) < ⊤ ∧
      -(1-tau) * (extendedEntropyNats (partialTraceSecond Z)).toReal ≤
        (qmi X).toReal - (qmi Z).toReal ∧
      (qmi X).toReal - (qmi Z).toReal ≤ (extendedEntropyNats (countableAverage mu)).toReal -
        tau * (extendedEntropyNats (partialTraceSecond Z)).toReal) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
