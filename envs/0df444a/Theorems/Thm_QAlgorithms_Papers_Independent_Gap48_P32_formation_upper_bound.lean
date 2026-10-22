-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P32_formation_upper_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P32.formation_upper_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:28:37.964058+00:00
-- url     : https://prove2.me/theorems/1c944dd4-9f8e-42a5-bf3e-51b1be734af8
-- title:
--   Entanglement of formation upper bound
-- statement:
--   All registers are finite and have positive dimension. Density matrices are positive semidefinite with trace one, all pure vectors have norm one, and entropy is in bits. Write $S$ for von Neumann entropy, $I(A;B)=S(A)+S(B)-S(AB)$, and $I(A;B|E)=S(AE)+S(BE)-S(E)-S(ABE)$. The squashed entanglement $E_{\mathrm{sq}}(\rho)$ is the infimum of $I(A;B|E)/2$ over every finite quantum extension of $\rho$, with no common dimension cap or attainment assumption. All marginals below are actual partial traces.
--
--   For every bipartite state $\rho$, let $E_F(\rho)$ be the infimum of $\sum_jp_jS(\operatorname{Tr}_B|\psi_j\rangle\langle\psi_j|)$ over all finite normalized pure-state ensembles averaging to $\rho$. Then $$E_{\mathrm{sq}}(\rho)\le E_F(\rho).$$ This compares unrestricted quantum extensions with the exact pure convex roof.
-- source:
--   "Squashed Entanglement" - An Additive Entanglement Measure, arXiv:quant-ph/0308088v3, PDF p. 3, §II, Proposition 5

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

/-- PDF p.3, Proposition 5: formation is the computed pure convex roof,
without any optimal-ensemble assumption. -/
theorem formation_upper_bound (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) : sq rho ≤ ef rho := by sorry

end Bipartite

end

end QAlgorithms.Papers.Independent.Gap48.P32
