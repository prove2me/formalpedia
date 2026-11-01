-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_exact_communication_lower
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.exact_communication_lower
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:05:51.687228+00:00
-- url     : https://prove2.me/theorems/f06ca88f-99ed-40f6-8cf7-690c25e04889
-- title:
--   Theorem 1: exact transformation communication lower bound
-- statement:
--   Let $\phi$ and $\psi$ be normalized finite-dimensional bipartite pure vectors, with Alice reductions $\phi_A=\operatorname{Tr}_B|\phi\rangle\langle\phi|$ and $\psi_A$ defined similarly. Write $\Delta(\rho)=\log_2(\operatorname{rank}\rho\,\lambda_{\max}(\rho))$. Every deterministic protocol transforming $\phi$ exactly into $\psi$, using local operations, local ancillas and quantum transfers of dimensions $d_i\ge1$, has cost $C=\sum_i\log_2 d_i$ satisfying
--
--   $$C\ge\tfrac12\bigl(\Delta(\psi_A)-\Delta(\phi_A)\bigr).$$
--
--   Local disposal is allowed and the tested final output is the unconditional pure target. This bound counts communication in either direction.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 3, Theorem 1: exact transformation communication lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P61

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P61

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (supportRank)

open QAlgorithms.Papers.Independent.Bridge50.P40 (entropyInfinity)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

attribute [local instance] Classical.propDecidable

section Operational

variable {A B C D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

/-- PDF p.3, Theorem 1: exact deterministic transformation lower bound. -/
theorem exact_communication_lower (phi : EuclideanSpace ℂ (A × B))
    (psi : EuclideanSpace ℂ (C × D)) (hphi : ‖phi‖ = 1) (hpsi : ‖psi‖ = 1)
    (cost : ℝ) (hprotocol : Quantum (pureDensity phi) (pureDensity psi) cost) :
    cost ≥ (spread (aliceDensity psi) - spread (aliceDensity phi)) / 2 := by sorry

end Operational

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
