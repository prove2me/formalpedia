-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P32_conditional_fannes_pure_pairs
-- name    : QAlgorithms.Papers.Independent.Gap48.P32.conditional_fannes_pure_pairs
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:41:32.758831+00:00
-- url     : https://prove2.me/theorems/6f08a12c-19db-4612-b092-4b2caa8e1a60
-- title:
--   Conditional Fannes bound for pairs of pure states
-- statement:
--   All registers are finite and have positive dimension. Density matrices are positive semidefinite with trace one, all pure vectors have norm one, and entropy is in bits. Write $S$ for von Neumann entropy, $I(A;B)=S(A)+S(B)-S(AB)$, and $I(A;B|E)=S(AE)+S(BE)-S(E)-S(ABE)$. The squashed entanglement $E_{\mathrm{sq}}(\rho)$ is the infimum of $I(A;B|E)/2$ over every finite quantum extension of $\rho$, with no common dimension cap or attainment assumption. All marginals below are actual partial traces.
--
--   Let $\psi,\phi$ be unit vectors on $A\otimes B$, let $\rho=|\psi\rangle\langle\psi|$, $\sigma=|\phi\rangle\langle\phi|$, and suppose $\|\rho-\sigma\|_1\le\epsilon$ with $\epsilon\ge0$. Then $$|S(A|B)_\rho-S(A|B)_\sigma|\le\eta(2\epsilon)+3\epsilon\log_2d_A,$$ with the same piecewise $\eta$ as in Lemma 13. This asserts the conjectured conditional-entropy bound for pure pairs, including entangled pairs whose reduced states may be mixed.
-- source:
--   "Squashed Entanglement" - An Additive Entanglement Measure, arXiv:quant-ph/0308088v3, PDF p. 8, Appendix A, final observation

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

/-- PDF p.8, Appendix A final observation: BOTH states are pure;
their reduced states need not be pure or classical. -/
theorem conditional_fannes_pure_pairs (psi phi : EuclideanSpace ℂ (A × B))
    (hpsi : ‖psi‖ = 1) (hphi : ‖phi‖ = 1)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hclose : traceNorm (pureDensity psi - pureDensity phi) ≤ epsilon) :
    |conditionalEntropy (pureDensity psi) - conditionalEntropy (pureDensity phi)| ≤
      fannesEta (2*epsilon) + 3*epsilon*Real.logb 2 (Fintype.card A) := by sorry

end Bipartite

end

end QAlgorithms.Papers.Independent.Gap48.P32
