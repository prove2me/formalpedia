-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_decouplingRecovery
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.decouplingRecovery
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:04:56.263773+00:00
-- url     : https://prove2.me/theorems/bfde4cc4-f497-4bb4-807c-a47d40959170
-- title:
--   §4, (7): recovery from reference–environment decoupling
-- statement:
--   Let $Q$ and $Q^{\prime}$ be finite complex Hilbert spaces of positive dimensions $M$ and $D$. A density operator is positive semidefinite with trace one. All logarithms and entropies are in bits. Write $\pi=I_Q/M$. For a nonzero code subspace $C\subset Q$ of dimension $K$, let $\pi_C=\Pi_C/K$. Write $F_e(C,\mathcal N)=\max_{\mathcal R}F_e(\pi_C,\mathcal R\circ\mathcal N)$, where $\mathcal R:B(Q^{\prime})\to B(Q)$ ranges over all CPTP recovery maps and state entanglement fidelity is squared and unconditional. Let $V:Q\to Q^{\prime}\otimes E$ satisfy $V^\dagger V\le I$ and represent $\mathcal N(X)=\operatorname{tr}_E(VXV^\dagger)$. Let $|\psi\rangle\in R\otimes Q$ have norm one and marginal $\pi_C$. Set $p=\operatorname{tr}\mathcal N(\pi_C)>0$, $\rho_R=\operatorname{tr}_Q|\psi\rangle\langle\psi|$, and $\omega=p^{-1}(I_R\otimes V)|\psi\rangle\langle\psi|(I_R\otimes V)^\dagger$. Put $\rho^{\prime}_{RE}=\operatorname{tr}_{Q^{\prime}}\omega$ and $\rho^{\prime}_E=\operatorname{tr}_{RQ^{\prime}}\omega$. Then
--
--   $$
--   F_e(C,\mathcal N)\ge p-p\|\rho^{\prime}_{RE}-\rho_R\otimes\rho^{\prime}_E\|_{\rm tr}.
--   $$
--
--   Small reference/environment correlation guarantees a good CPTP recovery.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 8, §4, (7): recovery from reference–environment decoupling

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P29

open QAlgorithms MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification coherentInformation singleUseInformation mixed)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Dependency50.P48 (wordProbability)

open QAlgorithms.Papers.Independent.Bridge50.P43 (tensorDensity)

open scoped Matrix ComplexConjugate ComplexOrder Topology

attribute [local instance] Classical.propDecidable

variable {I J E L : Type} [Fintype I] [DecidableEq I]

variable [Fintype J] [DecidableEq J] [Fintype E] [DecidableEq E]

variable [Fintype L] [DecidableEq L]

/-- PDF pp.8–10, (7)–(8): recovery from reference–environment decoupling.
The multiplier is p, not sqrt(p); only this normalized formulation requires p>0. -/
theorem decouplingRecovery [Nonempty I] [Nonempty J] [Nonempty E]
    {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
    (N : Superop I J) (V : Matrix (J × E) I ℂ)
    (hV : (1 - Vᴴ * V).PosSemidef)
    (hN : ∀ X, N X = traceRight (V * X * Vᴴ)) (C : CodeProjection I)
    (psi : EuclideanSpace ℂ (R × I)) (hpsi : ‖psi‖ = 1)
    (hpur : traceLeft (pureDensity psi) = codeDensity C)
    (hp : 0 < (N (codeDensity C)).trace.re) :
    let p := (N (codeDensity C)).trace.re
    let final := (p : ℂ)⁻¹ •
      (Matrix.kronecker (1 : Matrix R R ℂ) V * pureDensity psi *
        (Matrix.kronecker (1 : Matrix R R ℂ) V)ᴴ)
    let rhoRE := middlePartialTrace final
    p - p * traceNorm (rhoRE -
      Matrix.kronecker (traceRight (pureDensity psi)) (traceLeft rhoRE)) ≤
        recoveredEntanglementFidelity N (codeDensity C) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
