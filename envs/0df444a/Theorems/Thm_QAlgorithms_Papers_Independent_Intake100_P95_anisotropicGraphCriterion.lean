-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_anisotropicGraphCriterion
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.anisotropicGraphCriterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:50:31.186047+00:00
-- url     : https://prove2.me/theorems/84f9cfe3-d35c-4561-91ff-2666c6ac3f64
-- title:
--   Anisotropic XY inversion on a connected graph
-- statement:
--   Let $n\ge1$, let $J_{k\ell}$ be real couplings with connected nonzero support graph, and fix one common $\kappa\in[-1,1]$ for all edges. With identities understood on the remaining qubits, define
--
--   $$H_{XY}=\frac\pi2\sum_{k<\ell}J_{k\ell}(X_kX_\ell+\kappa Y_kY_\ell).$$
--
--   Then $H_{XY}$ is type-I locally reversible if and only if its support graph is bipartite or $\kappa=-1$. The endpoints, including $\kappa=0$, are retained. At $\kappa=-1$ any connected support graph is allowed.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 6, Lemma 6: anisotropic XX+κYY coupling graph

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- Lemma 6, PDF p.6, (26): one common kappa in [-1,1] on a connected
support graph. The endpoint -1 is the sole graph-independent exception. -/
theorem anisotropicGraphCriterion {n : ℕ} (hn : 0 < n)
    (J : Fin n → Fin n → ℝ) (hconnected : (couplingGraph J).Connected)
    (kappa : ℝ) (hkappa : -1 ≤ kappa ∧ kappa ≤ 1) :
    TypeI (networkXY J kappa) ↔ BipartiteCouplings J ∨ kappa = -1 := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
