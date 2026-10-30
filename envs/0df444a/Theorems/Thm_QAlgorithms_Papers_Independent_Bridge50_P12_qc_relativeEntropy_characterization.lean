-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P12_qc_relativeEntropy_characterization
-- name    : QAlgorithms.Papers.Independent.Bridge50.P12.qc_relativeEntropy_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:28:59.754492+00:00
-- url     : https://prove2.me/theorems/d5f4c1a2-ad22-4f9d-ac83-a6bf65855c7d
-- title:
--   Quantum–classical relative entropy discord: attained one-party dephasing formula
-- statement:
--   Let $\rho$ be a density operator on nonzero finite-dimensional systems $A\otimes B$. Let $D_{\rm qc}$ denote the infimum of extended relative entropy in bits over states classical on $B$, with arbitrary conditional density operators on $A$. If $\Delta_b$ dephases $B$ in an orthonormal basis $b$, then the following minimum is attained:
--
--   $$D_{\rm qc}(\rho)=\min_b H((\operatorname{id}_A\otimes\Delta_b)(\rho))-H(\rho).$$
--
--   The candidate dephased state is computed from $\rho$. This characterizes the oriented quantum–classical discord by an entropy minimum.
-- source:
--   Asymptotically Consistent Measures of General Quantum Resources: Discord, Non-Markovianity, and Non-Gaussianity, arXiv:2103.05665v4, PDF p. 14, Proposition S13

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P12

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Bridge50.P12

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

/-- PDF pp.14–15, Proposition S13, S40: attained entropy minimum over B bases
only; arbitrary quantum A blocks are retained. -/
theorem qc_relativeEntropy_characterization {A B : Type}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    ∃ V : Matrix.unitaryGroup B ℂ,
      normalizedResourceDistance quantumClassical rho ≠ ⊤ ∧
      (normalizedResourceDistance quantumClassical rho).toReal =
        vnEntropy (qcDephase V rho) - vnEntropy rho ∧
      ∀ V2 : Matrix.unitaryGroup B ℂ,
        vnEntropy (qcDephase V rho) ≤ vnEntropy (qcDephase V2 rho) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P12

end
