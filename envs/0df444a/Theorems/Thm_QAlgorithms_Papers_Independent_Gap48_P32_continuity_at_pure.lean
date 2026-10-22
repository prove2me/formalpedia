-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P32_continuity_at_pure
-- name    : QAlgorithms.Papers.Independent.Gap48.P32.continuity_at_pure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:33:25.662001+00:00
-- url     : https://prove2.me/theorems/90c90f98-e2c7-4a24-bc69-43f1ec2f2b5f
-- title:
--   Continuity at every pure state
-- statement:
--   All registers are finite and have positive dimension. Density matrices are positive semidefinite with trace one, all pure vectors have norm one, and entropy is in bits. Write $S$ for von Neumann entropy, $I(A;B)=S(A)+S(B)-S(AB)$, and $I(A;B|E)=S(AE)+S(BE)-S(E)-S(ABE)$. The squashed entanglement $E_{\mathrm{sq}}(\rho)$ is the infimum of $I(A;B|E)/2$ over every finite quantum extension of $\rho$, with no common dimension cap or attainment assumption. All marginals below are actual partial traces.
--
--   For every unit bipartite vector $\psi$ and every $\epsilon>0$, there is $\delta>0$ such that every density matrix $\rho$ with $\|\rho-|\psi\rangle\langle\psi|\|_1<\delta$ satisfies $$\left|E_{\mathrm{sq}}(\rho)-E_{\mathrm{sq}}(|\psi\rangle\langle\psi|)\right|<\epsilon.$$ The approach is through all density matrices on the fixed space. This pins the source’s pure-state continuity claim without claiming a whole open neighborhood of general continuity.
-- source:
--   "Squashed Entanglement" - An Additive Entanglement Measure, arXiv:quant-ph/0308088v3, PDF p. 4, §II, Remark 11

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P32

namespace QAlgorithms.Papers.Independent.Gap48.P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

local notation "sq" => QAlgorithms.Papers.Independent.Dependency50.P19.squashed

local notation "cmi" => QAlgorithms.Papers.Independent.Dependency50.P19.conditionalMutual

local notation "mi" => QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation

local notation "ef" => QAlgorithms.Papers.Independent.Information100.P08.formation

-- Reuse exact accepted generic tensor pairing and partial traces.

open QAlgorithms.Papers.Independent.Next46.P42 (regroupProduct)

open QAlgorithms.Papers.Independent.Information100.P08 (firstPair secondPair)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

section Bipartite

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [instAne : Nonempty A] [instBne : Nonempty B]

include instAne instBne

/-- PDF p.4, Remark 11: continuity at each pure state from the entire state
space, not merely along pure states. -/
theorem continuity_at_pure (psi : EuclideanSpace ℂ (A × B)) (hpsi : ‖psi‖ = 1) :
    ContinuousWithinAt (fun rho : Matrix (A × B) (A × B) ℂ => sq rho)
      {rho | IsDensityMatrix rho} (pureDensity psi) := by sorry

end Bipartite

end

end QAlgorithms.Papers.Independent.Gap48.P32
