-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P76_pointwisePrivacyFunnel
-- name    : QAlgorithms.Papers.Independent.Information100.P76.pointwisePrivacyFunnel
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:01:29.024008+00:00
-- url     : https://prove2.me/theorems/a6d14cce-17bf-4144-a3fe-a077dfd064bb
-- title:
--   Corollary 4.3: pointwise smoothing and quantum privacy funnel
-- statement:
--   Fix a minimal normalized Kraus family for a CPTP map $\Phi$ on $\mathbb C^q$, $q\ge1$. For every fixed positive-definite input density matrix $\rho$, let $\chi_\rho$ be the reference-output state of its canonical purification. Let $k_{\rho,\varepsilon}$ be the infimum of $S(QA\mid Z)$ over all positive finite auxiliary dimensions, exact product $QZ$ marginal $\rho^\mathsf T\otimes\sigma_Z$, and half trace error at most $\varepsilon$ in the $QA$ marginal. Define $K_0(\rho)$ independently by exact equality of that marginal. Then
--
--   $$\lim_{\varepsilon\downarrow0}k_{\rho,\varepsilon}=K_0(\rho)=S(\chi_\rho)-P_{\rm q}^{\psi_{EQ}}(0),\qquad\kappa(\Phi)=\sup_{\rho>0}\bigl[S(\chi_\rho)-P_{\rm q}^{\psi_{EQ}}(0)\bigr].$$
--
--   The quantum privacy funnel optimizes $I(QA;Z)$ over channels $E\to Z$ with $I(Q;Z)=0$ in the pure Stinespring state $\psi_{QAE}$. Every normalized exact $QA$ extension, and only such an extension, is obtained by applying one of these channels to $E$; the parametrization of all extensions does not impose the zero-leakage constraint until the funnel optimization. Channels extend arbitrarily outside the support of the environment marginal, including when it is singular. No finite auxiliary bound, attained optimizer, or uniformity as $\rho$ approaches rank deficiency is asserted. This identifies the smoothed cost pointwise with the exact privacy-funnel functional.
-- source:
--   Bath dimension and initial entropy for closed repeated use of a quantum channel, arXiv:2609.18267v1, PDF p. 9, Corollary 4.3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P76

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P76

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open Filter

/-- PDF p.9, Corollary 4.3: pointwise smoothing and the quantum privacy funnel.
The exact extension parametrization also applies when the environment marginal is singular. -/
theorem pointwisePrivacyFunnel {q k : ℕ} (hq : 0 < q) (hk : 0 < k)
    (A : Fin k → Op q) (hA : IsKrausFamily A) (hminimal : LinearIndependent ℂ A) :
    (∀ rho : Op q, IsDensityMatrix rho → rho.PosDef →
      Tendsto (smoothedCost (krausApply A) rho) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (exactInputCost (krausApply A) rho))) ∧
    intrinsicCost (krausApply A) = sSup {v | ∃ rho : Op q,
      IsDensityMatrix rho ∧ rho.PosDef ∧
      v = vnEntropy (chi (krausApply A) rho) - privacyFunnel A rho} ∧
    (∀ (rho : Op q), IsDensityMatrix rho → rho.PosDef →
      exactInputCost (krausApply A) rho =
        vnEntropy (chi (krausApply A) rho) - privacyFunnel A rho) ∧
    (∀ (rho : Op q), IsDensityMatrix rho → rho.PosDef → ∀ z : ℕ, 0 < z →
      ∀ sigma : Matrix ((Fin q × Fin q) × Fin z) ((Fin q × Fin q) × Fin z) ℂ,
        (IsDensityMatrix sigma ∧ traceRight sigma = chi (krausApply A) rho) ↔
          ∃ Lambda : Superop (Fin k) (Fin z), IsChannel Lambda ∧
            sigma = channelExtension A rho Lambda) := by sorry

end QAlgorithms.Papers.Independent.Information100.P76

end
