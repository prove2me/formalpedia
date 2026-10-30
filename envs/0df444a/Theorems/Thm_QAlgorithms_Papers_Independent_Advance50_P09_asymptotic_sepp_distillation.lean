-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P09_asymptotic_sepp_distillation
-- name    : QAlgorithms.Papers.Independent.Advance50.P09.asymptotic_sepp_distillation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:36:07.37852+00:00
-- url     : https://prove2.me/theorems/5daa80f7-8eca-4541-9f96-041e74e17587
-- title:
--   Asymptotic SEPP distillation equals regularized relative entropy
-- statement:
--   Let $\rho$ be a normalized density operator on a finite multipartite Hilbert space $H=\bigotimes_{i=1}^{m+2}H_i$, where every local space has positive dimension. Separability means full multipartite separability. All logarithms are base two. Let $F(\alpha,\beta)=(\operatorname{Tr}\sqrt{\sqrt\alpha\,\beta\sqrt\alpha})^2$ be squared Uhlmann fidelity.
--
--   SEPP consists of actual completely positive trace-preserving maps that send every fully separable state to a fully separable state. The resource $\Psi_M$ is a rank-$M$ maximally entangled state shared by the first two parties, with one-dimensional resource registers at the remaining parties; every positive integer $M$ is allowed.
--
--   Write $E_R(\alpha)=\inf_{\sigma\in\mathcal S}D(\alpha\Vert\sigma)$ for relative entropy of entanglement in bits, with infinite relative entropy on support violations, and $E_R^\infty(\rho)=\lim_{n\to\infty}n^{-1}E_R(\rho^{\otimes n})$. Tensor powers keep the original parties: party $i$ holds $H_i^{\otimes n}$.
--
--   For $0\le\varepsilon<1$, define $E_{D,\mathrm{SEPP}}^{(1),\varepsilon}(\alpha)$ by optimizing $\log_2M$ subject to $F(\Lambda(\alpha),\Psi_M)\ge1-\varepsilon$. The ordinary iterated limit exists and
--
--   $$
--   E_D^{\mathrm{ne}}(\rho):=
--   \lim_{\varepsilon\downarrow0}\lim_{n\to\infty}
--   \frac{1}{n}E_{D,\mathrm{SEPP}}^{(1),\varepsilon}(\rho^{\otimes n})
--   =E_R^\infty(\rho).
--   $$
--
--   This gives the operational asymptotic distillation value for every finite multipartite state. Copy numbers are positive, and both ordinary limits are asserted to exist.
-- source:
--   One-shot rates for entanglement manipulation under non-entangling maps, arXiv:0905.2673v2, PDF p. 3, Consequence after Eq.(23)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P09

noncomputable section

open Filter Set

open scoped Topology Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P09

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

/-- PDF p.3, the consequence after Eq.(23): ordinary iterated operational limit equals
ordinary regularized relative entropy, with copy number positive and error decreasing to zero. -/
theorem asymptotic_sepp_distillation {m : ℕ} (H : MultipartiteSystem m) (rho : MultipartiteOperator H)
    (hrho : IsDensityMatrix rho) :
    ∃ r : ℝ, HasDistillationLimit rho r ∧ HasRelativeLimit rho r := by sorry

end QAlgorithms.Papers.Independent.Advance50.P09

end
