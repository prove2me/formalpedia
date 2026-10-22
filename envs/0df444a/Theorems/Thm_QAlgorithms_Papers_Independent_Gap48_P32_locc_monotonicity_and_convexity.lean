-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P32_locc_monotonicity_and_convexity
-- name    : QAlgorithms.Papers.Independent.Gap48.P32.locc_monotonicity_and_convexity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:27:53.060006+00:00
-- url     : https://prove2.me/theorems/d7342f4b-08b8-4b61-b8a3-f28e55ba3de8
-- title:
--   Selective LOCC monotonicity and convexity
-- statement:
--   All registers are finite and have positive dimension. Density matrices are positive semidefinite with trace one, all pure vectors have norm one, and entropy is in bits. Write $S$ for von Neumann entropy, $I(A;B)=S(A)+S(B)-S(AB)$, and $I(A;B|E)=S(AE)+S(BE)-S(E)-S(ABE)$. The squashed entanglement $E_{\mathrm{sq}}(\rho)$ is the infimum of $I(A;B|E)/2$ over every finite quantum extension of $\rho$, with no common dimension cap or attainment assumption. All marginals below are actual partial traces.
--
--   Every finite adaptive two-way LOCC tree applied to $\rho$, with normalized leaf states $\rho_j$ and probabilities $p_j$, obeys $$\sum_jp_jE_{\mathrm{sq}}(\rho_j)\le E_{\mathrm{sq}}(\rho).$$ Zero-probability leaves contribute zero. For any states $\rho,\sigma$ on the same space and $0\le t\le1$, $$E_{\mathrm{sq}}(t\rho+(1-t)\sigma)\le tE_{\mathrm{sq}}(\rho)+(1-t)E_{\mathrm{sq}}(\sigma).$$ In particular, deterministic LOCC cannot increase the measure. These properties capture the average monotonicity and convexity used by the source.
-- source:
--   "Squashed Entanglement" - An Additive Entanglement Measure, arXiv:quant-ph/0308088v3, PDF p. 2, §II, Proposition 3

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

/-- PDF p.2, Proposition 3: selective adaptive LOCC monotonicity on average
(including deterministic outputs), and convexity for every binary mixture. -/
theorem locc_monotonicity_and_convexity :
    QAlgorithms.Papers.Independent.Claimed50.P33.IsAdaptiveLOCCMonotone
      (fun s => sq (pairOfState s)) ∧
    (∀ a b : ℕ, 0 < a → 0 < b →
      ∀ rho sigma : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
        IsDensityMatrix rho → IsDensityMatrix sigma →
        ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        sq (t • rho + (1-t) • sigma) ≤ t*sq rho + (1-t)*sq sigma) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P32
