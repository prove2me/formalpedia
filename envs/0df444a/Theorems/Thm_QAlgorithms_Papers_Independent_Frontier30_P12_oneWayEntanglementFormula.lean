-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P12_oneWayEntanglementFormula
-- name    : QAlgorithms.Papers.Independent.Frontier30.P12.oneWayEntanglementFormula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:12:31.141398+00:00
-- url     : https://prove2.me/theorems/b4c0e7b7-ecf3-4894-8f7b-a8d55bde5ec9
-- title:
--   Theorem 13: regularized one-way entanglement capacity
-- statement:
--   For a normalized bipartite density operator $\rho^{AB}$ on finite positive-dimensional complex registers, let $D_{\to}(\rho)$ be the operational one-way EPR capacity over evaluated finite CP instruments on Alice and transcript-dependent CPTP maps on Bob, acting on independent copies with no additional shared state. Then
--
--   $$D_{\to}(\rho)=\lim_{n\to\infty}\frac1nD^{(1)}(\rho^{\otimes n}),\qquad D^{(1)}(\rho)=\max_{\mathcal T}\sum_\ell\lambda_\ell I_c(A'\rangle B)_{\rho_\ell}.$$
--
--   The optimization is over all finite quantum instruments on Alice, including arbitrary finite output dimension. Its actual output blocks are $s_\ell=(\mathcal T_\ell\otimes\operatorname{id})(\rho)$, $\lambda_\ell=\operatorname{Tr}s_\ell$, and $\rho_\ell=s_\ell/\lambda_\ell$ when $\lambda_\ell>0$; zero-weight branches have fixed normalized conditional versions and contribute zero. Here $I_c(A'\rangle B)=H(B)-H(A'B)$ in bits.
--
--   The maximum is attained with $L\le d_A^2$ and one square positive Kraus operator per branch, $\mathcal T_\ell(\sigma)=A_\ell\sigma A_\ell^\dagger$ on the original Alice space. For each $n$-copy term this gives $L\le d_A^{2n}$. These are conclusions about an optimizer, not restrictions imposed on the unrestricted optimization.
--
--   This characterizes the operational capacity and proves finite-outcome attainment.
-- source:
--   Distillation of secret key and entanglement from quantum states, arXiv:quant-ph/0306078v1, PDF p. 9, Theorem 13

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P12

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- arXiv:quant-ph/0306078v1, PDF p.9, Theorem 13. The maximum ranges over
all finite CP instruments; single-Kraus/range restrictions are conclusions.
Zero-mass branches have fixed normalized versions and contribute zero. -/
theorem oneWayEntanglementFormula {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Op (A × B))
    (h : QAlgorithms.IsDensityMatrix rho) :
    Tendsto (fun n => entSingle (bipCopies rho n) / n) atTop (nhds (entCapacity rho)) ∧
    (∀ n : ℕ, 0 < n → EntRestrictedMaximum (bipCopies rho n)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P12

end
