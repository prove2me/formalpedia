-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P15_petz_mutual_information_formula
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P15.petz_mutual_information_formula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:06:15.766547+00:00
-- url     : https://prove2.me/theorems/b9e3a7b5-0094-4d0f-8237-a332c6b66989
-- title:
--   Explicit Petz mutual information and its minimizing state
-- statement:
--   All Hilbert spaces are finite-dimensional and nonzero. A density operator is positive semidefinite with trace one; singular states are included. All logarithms are base two. For real $\alpha>1$, $\widetilde D_\alpha$ denotes the sandwiched Rényi divergence and $D_\alpha$ the traditional Petz divergence, with value $+\infty$ on support failure and negative spectral powers taken on the support.
--
--   For a bipartite density $\rho_{AB}$, let $\rho_A=\operatorname{Tr}_B\rho_{AB}$ and put $K_\alpha=\operatorname{Tr}_A[((\rho_A^{(1-\alpha)/2})\otimes I_B)\rho_{AB}^\alpha((\rho_A^{(1-\alpha)/2})\otimes I_B)]$, $Z_\alpha=\operatorname{Tr}K_\alpha^{1/\alpha}$, and $\sigma_B^*=K_\alpha^{1/\alpha}/Z_\alpha$. Partial-trace cyclicity gives $K_\alpha=\operatorname{Tr}_A[(\rho_A^{1-\alpha}\otimes I_B)\rho_{AB}^\alpha]$.
--
--   The quantity $I_\alpha(A;B)_\rho=\inf_{\sigma_B}D_\alpha(\rho_{AB}\Vert\rho_A\otimes\sigma_B)$ has the finite explicit value
--
--   $$I_\alpha(A;B)_\rho=\frac\alpha{\alpha-1}\log_2 Z_\alpha.$$
--
--   Here $Z_\alpha>0$ and $\sigma_B^*$ is a density attaining that infimum. Thus the source minimum includes singular inputs. The formula expresses state mutual information through a single partial trace and spectral root.
-- source:
--   Multiplicativity of completely bounded $p$-norms implies a strong converse for entanglement-assisted capacity, arXiv:1310.7028v3, PDF p. 15, Corollary 8: explicit Petz mutual information, (6.20)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P15

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Topology

open Filter

namespace QAlgorithms.Papers.Independent.Intakenext100.P15

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- These are pinned accepted definitions, not other chunks from the current run.

open QAlgorithms.Papers.Independent.Bridge50.P43 (NormalizedDensity payoff)

open QAlgorithms.Papers.Independent.Dependency50.P09 (Divergence logExt sandwichedD petzD)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten)

open QAlgorithms.Papers.Independent.Information100.P71
  (supportPower SupportIncluded stateRelative channelPower diamond)

/-- PDF p.15, Corollary 8, (6.20)--(6.24). The minimum is attained by the
explicit normalized Sibson state, including rank-deficient inputs. -/
theorem petz_mutual_information_formula
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (rho : NormalizedDensity (A × B)) (alpha : ℝ) (ha : 1 < alpha) :
    0 < sibsonZ alpha rho.1 ∧ IsDensityMatrix (sibsonState alpha rho.1) ∧
    stateInfo (petzD alpha) rho.1 =
      ((alpha / (alpha - 1) * Real.logb 2 (sibsonZ alpha rho.1) : ℝ) : EReal) ∧
    petzD alpha rho.1 (Matrix.kronecker (traceRight rho.1) (sibsonState alpha rho.1)) =
      stateInfo (petzD alpha) rho.1 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P15

end
