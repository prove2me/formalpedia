-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P36_relativeEntropy_convexMonotone
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P36.relativeEntropy_convexMonotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:22:12.337028+00:00
-- url     : https://prove2.me/theorems/497fb41a-0fc7-4ca1-b205-04c3d7cb59cc
-- title:
--   Relative entropy of steering is a convex steering monotone
-- statement:
--   For normalized assemblages \(\rho,\sigma\) with the same finite alphabets and Bob space, let \(S_A(\rho\|\sigma)\) be the optimized distinguishability in (18). It maximizes, over every complete Bob instrument \(\{E_\gamma\}\) and every normalized input kernel \(P(x|\gamma)\), the sum of \(D_{\mathrm{KL}}(p\|q)\) and
--   \(\sum_{\gamma,x}P(x|\gamma)p_\gamma D(E_\gamma\widehat\rho(x)E_\gamma^\dagger/p_\gamma\|E_\gamma\widehat\sigma(x)E_\gamma^\dagger/q_\gamma)\).
--   Here \(\widehat\rho(x)=\sum_a|a\rangle\langle a|\otimes\rho_{a|x}\), \(p_\gamma=\operatorname{Tr}(E_\gamma\rho_BE_\gamma^\dagger)\), and \(q_\gamma\) is computed from \(\sigma_B\). All logarithms are natural, support failures have divergence \(+\infty\), and zero-weight terms vanish. Define
--
--   $$
--   S_R(\rho)=\min_{\sigma\in\mathrm{LHS},\ \operatorname{Tr}\sigma=1}S_A(\rho\|\sigma).
--   $$
--
--   The stated maxima and minima are attained, and \(S_R\) is finite, nonnegative, zero on LHS, convex, and nonincreasing on average under every complete 1W-LOCC instrument. Convexity includes both endpoints; averaging uses the first assemblage’s outcome law and positive-mass conditional outputs. These properties make \(S_R\) a convex steering monotone; no converse to vanishing on LHS is asserted.
-- source:
--   The resource theory of steering, arXiv:1409.5804v3, PDF p. 6, Theorem 2, (18),(20)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P36

noncomputable section

open scoped BigOperators ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P36

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable

variable {d r s df rf sf m : ℕ}

/-- Theorem 2, PDF p.6, (18),(20); proof pp.10–11. The extrema written as
max/min in the source are retained as explicit attainment obligations. The
steering value is finite; pairwise assemblage divergence may be infinite. -/
theorem relativeEntropy_convexMonotone :
    (∀ (d r s : ℕ) (rho sigma : AssemblageBlocks d r s),
      IsNormalized rho → IsNormalized sigma → EntropyMaximum rho sigma) ∧
    (∀ (d r s : ℕ) (rho : AssemblageBlocks d r s), IsNormalized rho →
      steeringEntropy rho ≠ ⊤ ∧ ∃ sigma : AssemblageBlocks d r s,
        IsNormalized sigma ∧ HasFiniteLHSModel sigma ∧
        assemblageEntropy rho sigma = steeringEntropy rho) ∧
    IsConvexSteeringMonotone relativeEntropyMeasure := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P36

end
