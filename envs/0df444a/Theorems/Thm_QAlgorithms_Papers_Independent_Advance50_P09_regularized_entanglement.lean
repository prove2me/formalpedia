-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P09_regularized_entanglement
-- name    : QAlgorithms.Papers.Independent.Advance50.P09.regularized_entanglement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:32:43.862801+00:00
-- url     : https://prove2.me/theorems/ea750682-052f-470b-9445-753d17099d17
-- title:
--   Equality of regularized smoothed entanglement measures
-- statement:
--   Let $\rho$ be a normalized density operator on a finite multipartite Hilbert space $H=\bigotimes_{i=1}^{m+2}H_i$, where every local space has positive dimension. Separability means full multipartite separability. All logarithms are base two. Let $F(\alpha,\beta)=(\operatorname{Tr}\sqrt{\sqrt\alpha\,\beta\sqrt\alpha})^2$ be squared Uhlmann fidelity.
--
--   Here $E_{\min}^{\varepsilon}(\rho)=\max_{0\le A\le I,\,\operatorname{Tr}(A\rho)\ge1-\varepsilon}\min_{\sigma\in\mathcal S(H)}[-\log_2\operatorname{Tr}(A\sigma)]$ is the operator-smoothed min-relative entropy of entanglement, with $-\log_2 0=+\infty$.
--
--   Here $E_{\max}(\alpha)=\inf_{\sigma\in\mathcal S}\inf\{\log_2 s:\alpha\le s\sigma\}$ and $E_{\max}^{\varepsilon}(\alpha)=\min\{E_{\max}(\beta):\beta\text{ is normalized},\ F(\beta,\alpha)\ge1-\varepsilon\}$.
--
--   Write $E_R(\alpha)=\inf_{\sigma\in\mathcal S}D(\alpha\Vert\sigma)$ for relative entropy of entanglement in bits, with infinite relative entropy on support violations, and $E_R^\infty(\rho)=\lim_{n\to\infty}n^{-1}E_R(\rho^{\otimes n})$. Tensor powers keep the original parties: party $i$ holds $H_i^{\otimes n}$.
--
--   For positive copy numbers define
--   $\mathcal E_{\min}^{\varepsilon}(\rho)=\liminf_{n\to\infty}n^{-1}E_{\min}^{\varepsilon}(\rho^{\otimes n})$ and
--   $\mathcal E_{\max}^{\varepsilon}(\rho)=\limsup_{n\to\infty}n^{-1}E_{\max}^{\varepsilon}(\rho^{\otimes n})$.
--   Let $\mathcal E_{\min}(\rho)=\lim_{\varepsilon\downarrow0}\mathcal E_{\min}^{\varepsilon}(\rho)$ and analogously define $\mathcal E_{\max}(\rho)$. The ordinary limits in these definitions exist, are finite, and
--
--   $$
--   \mathcal E_{\min}(\rho)=\mathcal E_{\max}(\rho)=E_R^\infty(\rho).
--   $$
--
--   The identity connects regularized test distinguishability and smoothed max entanglement to relative entropy. No entanglement or full-rank assumption is required.
--
--   **Formalization Note** Lean asserts a common real limit via three explicit limit predicates, retaining liminf for min and limsup for max. It does not use an arbitrary default value for a nonexistent ordinary limit.
-- source:
--   One-shot rates for entanglement manipulation under non-entangling maps, arXiv:0905.2673v2, PDF p. 3, Theorem 4, Eq.(22)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P09

noncomputable section

open Filter Set

open scoped Topology Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P09

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

/-- PDF pp.3,6, Theorem 4, Eq.(22): all three independently defined regularizations
have one finite common limit; neither the cited max identity nor Lemma 4 is assumed. -/
theorem regularized_entanglement {m : ℕ} (H : MultipartiteSystem m) (rho : MultipartiteOperator H)
    (hrho : IsDensityMatrix rho) :
    ∃ r : ℝ, HasMinLimit rho r ∧ HasMaxLimit rho r ∧ HasRelativeLimit rho r := by sorry

end QAlgorithms.Papers.Independent.Advance50.P09

end
