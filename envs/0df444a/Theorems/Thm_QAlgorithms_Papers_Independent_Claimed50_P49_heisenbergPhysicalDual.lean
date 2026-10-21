-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_heisenbergPhysicalDual
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.heisenbergPhysicalDual
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:03:03.723814+00:00
-- url     : https://prove2.me/theorems/2919e86a-c351-4f2c-b5e3-33cb09f7b119
-- title:
--   Normal Heisenberg physical duals and recovery identities
-- statement:
--   A physical representation consists of one fixed bounded unitary $U$ on the completed system–environment tensor product and one fixed environment density $\sigma$, independent of the input. Write $E(\rho)=\operatorname{Tr}_B U(\rho\otimes\sigma)U^\dagger$ and $F(\rho)=\operatorname{Tr}_A U(\rho\otimes\sigma)U^\dagger$. There exist normal complex-linear CP unital maps $H:\mathcal B(A)\to\mathcal B(A)$ and $\widetilde H:\mathcal B(B)\to\mathcal B(A)$, the respective trace duals of $E,F$. For every density $\rho$ and bounded observables $X,Y$,
--
--   $$\operatorname{Tr}\rho H(X)=\operatorname{Tr}(\rho\otimes\sigma)U^\dagger(X\otimes I)U,$$
--   $$\operatorname{Tr}\rho\widetilde H(Y)=\operatorname{Tr}(\rho\otimes\sigma)U^\dagger(I\otimes Y)U.$$
--
--   Every CPTP recovery $R$ has a normal CP unital trace dual $R_H$. The identities $R\circ E=F$ and $R\circ F=E$ are respectively equivalent to $H\circ R_H=\widetilde H$ and $\widetilde H\circ R_H=H$, with the appropriate recovery direction. This is the bounded-observable version of weak and anti-degradability.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 5, (1.6)–(1.10)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P49

noncomputable section

open scoped BigOperators ENNReal Topology

open Filter MeasureTheory

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

namespace QAlgorithms.Papers.Independent.Claimed50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Equations (1.6)-(1.10), PDF p.5: normal CP unital physical duals.
Printed (1.8) has an unmatched parenthesis. The bounded expression below uses
U-adjoint(1 tensor Theta)U, evaluated by the weighted state pairing, so no
infinite-dimensional unweighted partial trace of 1 tensor sigma is taken. -/
theorem heisenbergPhysicalDual {I J : Type} [Nonempty I]
    (U : Hilbert (I × J) ≃ₗᵢ[ℂ] Hilbert (I × J)) (sigma : State J) :
    ∃ (H : BoundedOp I → BoundedOp I) (F : BoundedOp J → BoundedOp I),
      IsBoundedCPUnital H ∧ IsBoundedCPUnital F ∧
      TraceDual (dilationReceiver U sigma.coefficients) H ∧
      TraceDual (weakComplement U sigma.coefficients) F ∧
      (∀ (rho : State I) (T : BoundedOp I),
        traceClassObservablePair rho.coefficients (observableCoeff (H T)) =
          traceClassObservablePair (productCoeff rho.coefficients sigma.coefficients)
            (boundedUnitaryConjugation U.symm
              (productCoeff (observableCoeff T) (identityCoeff J)))) ∧
      (∀ (rho : State I) (T : BoundedOp J),
        traceClassObservablePair rho.coefficients (observableCoeff (F T)) =
          traceClassObservablePair (productCoeff rho.coefficients sigma.coefficients)
            (boundedUnitaryConjugation U.symm
              (productCoeff (identityCoeff I) (observableCoeff T)))) ∧
      (∀ (R : Operation I J), IsTraceClassChannel R →
        ∃ G : BoundedOp J → BoundedOp I,
          IsBoundedCPUnital G ∧ TraceDual R G ∧
          ((∀ rho : State I, R (dilationReceiver U sigma.coefficients rho.coefficients) =
              weakComplement U sigma.coefficients rho.coefficients) ↔
            ∀ T : BoundedOp J, H (G T) = F T)) ∧
      (∀ (R : Operation J I), IsTraceClassChannel R →
        ∃ G : BoundedOp I → BoundedOp J,
          IsBoundedCPUnital G ∧ TraceDual R G ∧
          ((∀ rho : State I, R (weakComplement U sigma.coefficients rho.coefficients) =
              dilationReceiver U sigma.coefficients rho.coefficients) ↔
            ∀ T : BoundedOp I, F (G T) = H T)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
