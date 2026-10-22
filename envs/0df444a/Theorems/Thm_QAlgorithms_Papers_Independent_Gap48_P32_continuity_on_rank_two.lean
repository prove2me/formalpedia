-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P32_continuity_on_rank_two
-- name    : QAlgorithms.Papers.Independent.Gap48.P32.continuity_on_rank_two
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:39:51.957714+00:00
-- url     : https://prove2.me/theorems/76d3361d-4db5-4600-905f-4d6e38706e62
-- title:
--   Continuity on the entire rank-two stratum
-- statement:
--   All registers are finite and have positive dimension. Density matrices are positive semidefinite with trace one, all pure vectors have norm one, and entropy is in bits. Write $S$ for von Neumann entropy, $I(A;B)=S(A)+S(B)-S(AB)$, and $I(A;B|E)=S(AE)+S(BE)-S(E)-S(ABE)$. The squashed entanglement $E_{\mathrm{sq}}(\rho)$ is the infimum of $I(A;B|E)/2$ over every finite quantum extension of $\rho$, with no common dimension cap or attainment assumption. All marginals below are actual partial traces.
--
--   On the fixed bipartite space, $$E_{\mathrm{sq}}\big|_{\{\rho\in\mathcal D:\operatorname{rank}\rho=2\}}\text{ is continuous}.$$ Supports may vary within this domain. This records the source’s additional stratum continuity claim; when the space has dimension below two, the domain is empty.
-- source:
--   "Squashed Entanglement" - An Additive Entanglement Measure, arXiv:quant-ph/0308088v3, PDF p. 6, §IV, consequence after Proposition 16

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

/-- PDF p.6, unnumbered consequence after Proposition 16: all rank-two states,
with varying supports, equipped with their restricted-domain topology. -/
theorem continuity_on_rank_two :
    ContinuousOn (fun rho : Matrix (A × B) (A × B) ℂ => sq rho)
      {rho | IsDensityMatrix rho ∧ rho.rank = 2} := by sorry

end Bipartite

end

end QAlgorithms.Papers.Independent.Gap48.P32
