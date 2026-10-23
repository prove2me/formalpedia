-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_normalizedCP_encodingReplacement
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.normalizedCP_encodingReplacement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:23:55.459835+00:00
-- url     : https://prove2.me/theorems/cbed06f8-959c-436e-a2aa-a79b2e774d0d
-- title:
--   Proposition 5.1 / (70),(71): normalized CP encoding replacement
-- statement:
--   Let $H,K$ have finite dimensions $\eta,\kappa\ge1$, let $\rho$ be a density matrix on $H$, let $E:H\to K$ be completely positive with $\operatorname{tr}E(\rho)=1$, and let $T:K\to H$ be CPTP. No trace condition on $E$ at other inputs is assumed. There exists a CPTP replacement $\widetilde E$ such that
--   $$F_e(\rho,T\widetilde E)\ge F_e(\rho,TE)^2.$$
--   If $\eta\le\kappa$, it has the form $\widetilde E(X)=VXV^*$ for an isometry $V:H\to K$. If $\eta>\kappa$, it has the form
--   $$\widetilde E(X)=W^*XW+\frac{\operatorname{tr}((I_H-WW^*)X)}{\kappa}I_K$$
--   for an isometry $W:K\to H$. Fidelity is the unnormalized squared CP-map formula. Both dimensional branches belong to the replacement result.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 20, Proposition 5.1 / (70),(71): normalized CP encoding replacement

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P07

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap20.P07

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize rankOne tensorApply)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation isometryCoeff conjugateKernel)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (stabilizedTraceClassNorm traceClassTensorMap traceClassChannelPower
   transpose transposeBound TraceLinear tracePair MeasurePrepare)

open QAlgorithms.Papers.Independent.Gap48.P29 (fe FiniteCPMap)

/-- PDF pp.20--22, Proposition 5.1, (70)--(71): E is CP and normalized only on
rho. Both dimension branches and their isometry directions are retained. -/
theorem normalizedCP_encodingReplacement (eta kappa : ℕ) (heta : 0 < eta) (hkappa : 0 < kappa)
    (rho : Matrix (Fin eta) (Fin eta) ℂ) (hrho : IsDensityMatrix rho)
    (E : Superop (Fin eta) (Fin kappa)) (hE : FiniteCPMap E) (htrace : (E rho).trace = 1)
    (T : Superop (Fin kappa) (Fin eta)) (hT : IsChannel T) :
    ∃ replacement : Superop (Fin eta) (Fin kappa), IsChannel replacement ∧
      (fe rho (T ∘ E))^2 ≤ fe rho (T ∘ replacement) ∧
      (eta ≤ kappa → ∃ V : Matrix (Fin kappa) (Fin eta) ℂ,
        V.conjTranspose * V = 1 ∧ ∀ X, replacement X = V * X * V.conjTranspose) ∧
      (kappa < eta → ∃ W : Matrix (Fin eta) (Fin kappa) ℂ,
        W.conjTranspose * W = 1 ∧ ∀ X,
          replacement X = W.conjTranspose * X * W +
            ((((1 - W * W.conjTranspose) * X).trace / (kappa : ℂ))) • 1) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
