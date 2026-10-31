-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P15_quantum_sibson_identity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P15.quantum_sibson_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:05:17.398996+00:00
-- url     : https://prove2.me/theorems/f0a2df66-cc71-4549-b1b4-45157c28efb9
-- title:
--   Quantum Sibson identity for the Petz divergence
-- statement:
--   All Hilbert spaces are finite-dimensional and nonzero. A density operator is positive semidefinite with trace one; singular states are included. All logarithms are base two. For real $\alpha>1$, $\widetilde D_\alpha$ denotes the sandwiched Rényi divergence and $D_\alpha$ the traditional Petz divergence, with value $+\infty$ on support failure and negative spectral powers taken on the support.
--
--   For a bipartite density $\rho_{AB}$, let $\rho_A=\operatorname{Tr}_B\rho_{AB}$ and put $K_\alpha=\operatorname{Tr}_A[((\rho_A^{(1-\alpha)/2})\otimes I_B)\rho_{AB}^\alpha((\rho_A^{(1-\alpha)/2})\otimes I_B)]$, $Z_\alpha=\operatorname{Tr}K_\alpha^{1/\alpha}$, and $\sigma_B^*=K_\alpha^{1/\alpha}/Z_\alpha$. Partial-trace cyclicity gives $K_\alpha=\operatorname{Tr}_A[(\rho_A^{1-\alpha}\otimes I_B)\rho_{AB}^\alpha]$.
--
--   For every density $\sigma_B$ and every $\alpha>1$, the normalization satisfies $Z_\alpha>0$, the constructed $\sigma_B^*$ is a density, and
--
--   $$D_\alpha(\rho_{AB}\Vert\rho_A\otimes\sigma_B)=D_\alpha(\sigma_B^*\Vert\sigma_B)+D_\alpha(\rho_{AB}\Vert\rho_A\otimes\sigma_B^*).$$
--
--   The equality holds in the extended reals for singular comparisons as well. This decomposition supplies the explicit minimizing comparison state for Petz mutual information.
-- source:
--   Multiplicativity of completely bounded $p$-norms implies a strong converse for entanglement-assisted capacity, arXiv:1310.7028v3, PDF p. 14, Lemma 7 (Quantum Sibson identity), (6.7)–(6.8)

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

/-- PDF pp.14--15, Lemma 7, (6.7)--(6.8). Z>0 and normalization are conclusions;
the optimizer is constructed from the actual marginal and retains singular comparisons. -/
theorem quantum_sibson_identity
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (rho : NormalizedDensity (A × B)) (sigma : NormalizedDensity B)
    (alpha : ℝ) (ha : 1 < alpha) :
    0 < sibsonZ alpha rho.1 ∧ IsDensityMatrix (sibsonState alpha rho.1) ∧
    sibsonK alpha rho.1 =
      traceLeft (Matrix.kronecker (supportPower (traceRight rho.1) (1 - alpha))
        (1 : Matrix B B ℂ) * supportPower rho.1 alpha) ∧
    petzD alpha rho.1 (Matrix.kronecker (traceRight rho.1) sigma.1) =
      petzD alpha (sibsonState alpha rho.1) sigma.1 +
        petzD alpha rho.1 (Matrix.kronecker (traceRight rho.1) (sibsonState alpha rho.1)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P15

end
