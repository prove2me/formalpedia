-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_relativeEntropy_pinch_le
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.relativeEntropy_pinch_le
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-29T00:09:54.41522+00:00
-- url     : https://prove2.me/theorems/f514dbe1-607a-4909-9b28-d9af3cfdf1bf
-- title:
--   §VI, proof of Lemma 8: relative entropy does not increase under pinching
-- statement:
--   All matrices are $d\times d$ complex matrices. A state is a positive semidefinite matrix with trace one. $D(\rho\|\sigma)$ denotes the support-aware Umegaki relative entropy $\operatorname{Tr}\rho\log\rho-\operatorname{Tr}\rho\log\sigma$ (natural logarithms, $0\log0=0$), valued in the extended reals, with value $+\infty$ when $\ker\sigma\not\subseteq\ker\rho$. Let $U$ be a $d\times d$ unitary and let $\mathcal P_U(X)=U\,\operatorname{Diag}(U^\dagger XU)\,U^\dagger$ be the pinching (complete dephasing) in the orthonormal basis given by the columns of $U$. Here $\operatorname{Diag}$ sets all off-diagonal entries to zero.
--
--   **Claim.** For all states $\rho,\sigma$, $D(\mathcal P_U(\rho)\|\mathcal P_U(\sigma))\le D(\rho\|\sigma)$. This is the monotonicity of the relative entropy under this completely positive trace-preserving map, including the value $+\infty$.
-- source:
--   Continuity bounds on the quantum relative entropy, Audenaert–Eisert, arXiv:quant-ph/0503218v3, PDF pp. 6–7, §VI, Eq. (21)–(22) and the proof of Lemma 8

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40


/-- PDF p.7, proof of Lemma 8: monotonicity of the Umegaki relative entropy under the
pinching (complete dephasing) `X ↦ U Diag(Uᴴ X U) Uᴴ` in an arbitrary orthonormal basis,
given by the columns of a unitary `U`. -/
theorem relativeEntropy_pinch_le {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (rho sigma : Mat d) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    relativeEntropy
        ((U : Mat d) * Matrix.diagonal (fun i => ((U : Mat d)ᴴ * rho * (U : Mat d)) i i) *
          (U : Mat d)ᴴ)
        ((U : Mat d) * Matrix.diagonal (fun i => ((U : Mat d)ᴴ * sigma * (U : Mat d)) i i) *
          (U : Mat d)ᴴ) ≤
      relativeEntropy rho sigma := by
  sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
