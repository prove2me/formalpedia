-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P09_asymptotic_catalytic_reversibility
-- name    : QAlgorithms.Papers.Independent.Advance50.P09.asymptotic_catalytic_reversibility
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:36:41.871986+00:00
-- url     : https://prove2.me/theorems/0dae16f9-eefd-424e-9bd3-ad61b2dda4ae
-- title:
--   Asymptotic catalytic reversibility
-- statement:
--   Let $\rho$ be a normalized density operator on a finite multipartite Hilbert space $H=\bigotimes_{i=1}^{m+2}H_i$, where every local space has positive dimension. Separability means full multipartite separability. All logarithms are base two. Let $F(\alpha,\beta)=(\operatorname{Tr}\sqrt{\sqrt\alpha\,\beta\sqrt\alpha})^2$ be squared Uhlmann fidelity.
--
--   SEPP consists of actual completely positive trace-preserving maps that send every fully separable state to a fully separable state. The resource $\Psi_M$ is a rank-$M$ maximally entangled state shared by the first two parties, with one-dimensional resource registers at the remaining parties; every positive integer $M$ is allowed.
--
--   Write $E_R(\alpha)=\inf_{\sigma\in\mathcal S}D(\alpha\Vert\sigma)$ for relative entropy of entanglement in bits, with infinite relative entropy on support violations, and $E_R^\infty(\rho)=\lim_{n\to\infty}n^{-1}E_R(\rho^{\otimes n})$. Tensor powers keep the original parties: party $i$ holds $H_i^{\otimes n}$.
--
--   For $\delta>0$, a delta-SEPP map is CPTP and produces global robustness at most $\delta$ on every separable input. Let $\widetilde E_{C,\delta\text{-}\mathrm{SEPP}}^{(1),\varepsilon}(\alpha)$ be the minimum of $\log_2 M$ over positive ranks $M,K$, normalized states $\alpha'$, and delta-SEPP channels satisfying
--   $\Lambda(\Psi_M\otimes\Psi_K)=\alpha'\otimes\Psi_K$ and $F(\alpha,\alpha')\ge1-\varepsilon$. Thus the catalyst is returned exactly and without correlation. Let $E_D^{\mathrm{ne}}$ be the ordinary iterated SEPP distillation rate from Eq.(23). All ordinary limits below exist, and
--
--   $$
--   E_C^{\mathrm{ane}}(\rho):=
--   \lim_{\varepsilon\downarrow0}\lim_{\delta\downarrow0}\lim_{n\to\infty}
--   \frac{1}{n}\widetilde E_{C,\delta\text{-}\mathrm{SEPP}}^{(1),\varepsilon}(\rho^{\otimes n})
--   =E_D^{\mathrm{ne}}(\rho)=E_R^\infty(\rho).
--   $$
--
--   This is the source's asymptotic catalytic reversibility claim, with catalyst rank optimized independently at each block.
--
--   **Formalization Note** The printed Eq.(24) omits the tensor power on $\rho$; it is restored from the many-copy context. The order of limits is unchanged. The separate fixed-catalyst ambiguity in finite-copy Theorem 3 is not assumed as a hypothesis here.
-- source:
--   One-shot rates for entanglement manipulation under non-entangling maps, arXiv:0905.2673v2, PDF p. 4, Consequence after Eq.(24)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P09

noncomputable section

open Filter Set

open scoped Topology Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P09

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

/-- PDF pp.3--4, consequence after Eq.(24): catalytic asymptotic cost and distillation
have the same regularized relative entropy value. The corrected Eq.(24) uses rho tensor n;
limits keep the order n, delta, epsilon and catalysts return exactly without correlations. -/
theorem asymptotic_catalytic_reversibility {m : ℕ} (H : MultipartiteSystem m) (rho : MultipartiteOperator H)
    (hrho : IsDensityMatrix rho) :
    ∃ r : ℝ, HasDistillationLimit rho r ∧ HasCatalyticLimit rho r ∧
      HasRelativeLimit rho r := by sorry

end QAlgorithms.Papers.Independent.Advance50.P09

end
