-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P36_assemblageEntropy_jointConvexity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P36.assemblageEntropy_jointConvexity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:25:23.841879+00:00
-- url     : https://prove2.me/theorems/2cb70981-387b-4d23-808f-6adc0922fb94
-- title:
--   Joint convexity of assemblage relative entropy
-- statement:
--   Let \(n>0\), and let \(\{\rho_j\}_{j=1}^n\) and \(\{\sigma_j\}_{j=1}^n\) be normalized no-signaling assemblages with the same finite dimensions and alphabets. For positive real weights \(\mu_j\) satisfying \(\sum_j\mu_j=1\), the relative entropy \(S_A\) defined in (18) obeys
--
--   $$
--   S_A\!\left(\sum_j\mu_j\rho_j\,\middle\|\,\sum_j\mu_j\sigma_j\right)
--   \le\sum_j\mu_jS_A(\rho_j\|\sigma_j).
--   $$
--
--   Both mixtures use exactly the same weights and finite index family. Divergences may be infinite. This is joint convexity of the source’s adaptive-instrument assemblage divergence, used in proving convexity of the relative entropy of steering.
-- source:
--   The resource theory of steering, arXiv:1409.5804v3, PDF p. 11, Appendix C, Lemma 2, (C2)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P36

noncomputable section

open scoped BigOperators ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P36

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable

variable {d r s df rf sf m : ℕ}

/-- Appendix C, Lemma 2, PDF p.11, (C2); proof pp.18–19. Positive weights on a
single nonempty finite family sum to one and mix both arguments identically. -/
theorem assemblageEntropy_jointConvexity {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hsum : ∑ j, p j = 1)
    (rho sigma : Fin n → AssemblageBlocks d r s)
    (hrho : ∀ j, IsNormalized (rho j)) (hsigma : ∀ j, IsNormalized (sigma j)) :
    assemblageEntropy (assemblageFamilyMixture p rho) (assemblageFamilyMixture p sigma) ≤
      ∑ j, ENNReal.ofReal (p j) * assemblageEntropy (rho j) (sigma j) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P36

end
