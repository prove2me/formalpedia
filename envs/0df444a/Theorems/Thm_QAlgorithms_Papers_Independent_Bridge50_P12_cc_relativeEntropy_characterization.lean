-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P12_cc_relativeEntropy_characterization
-- name    : QAlgorithms.Papers.Independent.Bridge50.P12.cc_relativeEntropy_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:27:28.241903+00:00
-- url     : https://prove2.me/theorems/e5cf85e2-4bd6-4daf-8999-c5d439705ae5
-- title:
--   Classical–classical relative entropy discord: attained dephasing formula
-- statement:
--   Let $A$ and $B$ be nonzero finite-dimensional quantum systems and let $\rho$ be a density operator on $A\otimes B$. Write $H$ for von Neumann entropy in bits, $D_{\rm cc}$ for the infimum of extended quantum relative entropy in bits over all classical–classical density operators, and $\Delta_a\otimes\Delta_b$ for dephasing in independent local orthonormal bases $a,b$. Then the following minimum is attained:
--
--   $$D_{\rm cc}(\rho)=\min_{a,b}H((\Delta_a\otimes\Delta_b)(\rho))-H(\rho).$$
--
--   All independent product outcomes are included. This identifies discord with the least entropy increase under local dephasing.
-- source:
--   Asymptotically Consistent Measures of General Quantum Resources: Discord, Non-Markovianity, and Non-Gaussianity, arXiv:2103.05665v4, PDF p. 13, Proposition S9

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P12

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Bridge50.P12

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

/-- PDF p.13, Proposition S9, S26. Correction D2.
Printed: one k labels both local ON bases in the sum. Changed: include every
independent product outcome in A × B. Why: equally labelled pairs give trace 1/2
for I4/4; S32–S35 require a normalized full outcome law. Round 1 independently
checked this minimal index correction. Minimizing bases are conclusions. -/
theorem cc_relativeEntropy_characterization {A B : Type}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    ∃ (U : Matrix.unitaryGroup A ℂ) (V : Matrix.unitaryGroup B ℂ),
      normalizedResourceDistance classicalClassical rho ≠ ⊤ ∧
      (normalizedResourceDistance classicalClassical rho).toReal =
        vnEntropy (ccDephase U V rho) - vnEntropy rho ∧
      ∀ (U2 : Matrix.unitaryGroup A ℂ) (V2 : Matrix.unitaryGroup B ℂ),
        vnEntropy (ccDephase U V rho) ≤ vnEntropy (ccDephase U2 V2 rho) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P12

end
