-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P32_conjecture_implies_continuity
-- name    : QAlgorithms.Papers.Independent.Gap48.P32.conjecture_implies_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:37:27.423197+00:00
-- url     : https://prove2.me/theorems/d2dd3720-b4f4-4d53-a0a7-faaefd2bd811
-- title:
--   Conjecture 14 implies continuity with the printed modulus
-- statement:
--   All registers are finite and have positive dimension. Density matrices are positive semidefinite with trace one, all pure vectors have norm one, and entropy is in bits. Write $S$ for von Neumann entropy, $I(A;B)=S(A)+S(B)-S(AB)$, and $I(A;B|E)=S(AE)+S(BE)-S(E)-S(ABE)$. The squashed entanglement $E_{\mathrm{sq}}(\rho)$ is the infimum of $I(A;B|E)/2$ over every finite quantum extension of $\rho$, with no common dimension cap or attainment assumption. All marginals below are actual partial traces.
--
--   Define $\eta(x)=-x\log_2x$ for $0\le x\le1/4$ and $\eta(x)=1/2$ for $x>1/4$, with $\eta(0)=0$. Assume Conjecture 14 uniformly over all finite positive dimensions: any pair of bipartite states at full trace norm distance at most $u\ge0$ obeys $|S(X|Y)_\rho-S(X|Y)_\sigma|\le\eta(2u)+3u\log_2 d_X$. If $\rho,\sigma$ on $A\otimes B$ satisfy $\|\rho-\sigma\|_1\le\epsilon$, $\epsilon\ge0$, then $$|E_{\mathrm{sq}}(\rho)-E_{\mathrm{sq}}(\sigma)|\le3\eta(2\sqrt\epsilon)+6\sqrt\epsilon\log_2(d_Ad_B).$$ In addition, $E_{\mathrm{sq}}$ is continuous on the whole fixed state set. This preserves the source’s conditional conclusion and deliberately loose printed bound.
-- source:
--   "Squashed Entanglement" - An Additive Entanglement Measure, arXiv:quant-ph/0308088v3, PDF p. 6, §IV, consequence of Conjecture 14

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

/-- PDF p.6, consequence of Conjecture 14: conditional on the dimension-uniform
entropy bound, retain the displayed loose modulus and full continuity. -/
theorem conjecture_implies_continuity (hconj : ConditionalFannesConjecture) :
    (∀ rho sigma : Matrix (A × B) (A × B) ℂ,
      IsDensityMatrix rho → IsDensityMatrix sigma →
      ∀ epsilon : ℝ, 0 ≤ epsilon → traceNorm (rho-sigma) ≤ epsilon →
      |sq rho - sq sigma| ≤ 3*fannesEta (2*Real.sqrt epsilon) +
        6*Real.sqrt epsilon*Real.logb 2 ((Fintype.card A : ℝ) * Fintype.card B)) ∧
    ContinuousOn (fun rho : Matrix (A × B) (A × B) ℂ => sq rho)
      {rho | IsDensityMatrix rho} := by sorry

end Bipartite

end

end QAlgorithms.Papers.Independent.Gap48.P32
