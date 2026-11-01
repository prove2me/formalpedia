-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_exact_renyi_gap_lower
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.exact_renyi_gap_lower
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:06:40.347565+00:00
-- url     : https://prove2.me/theorems/a70a4394-c19d-45d0-a2a7-f2102ef0cae7
-- title:
--   Remark 2: exact Renyi-gap communication bound
-- statement:
--   Let $\phi,\psi$ be normalized bipartite pure vectors and $0\le\alpha<\beta\le\infty$. For a density matrix $\rho$, let $S_a(\rho)$ be its base-two Rényi entropy, using support counting at zero, von Neumann entropy at one, and minus the logarithm of the largest eigenvalue at infinity. Set $\Delta^{\alpha\beta}=S_\alpha-S_\beta$. Every exact deterministic quantum transformation protocol of cost $C$ obeys
--
--   $$C\ge\tfrac12\bigl(\Delta^{\alpha\beta}(\psi_A)-\Delta^{\alpha\beta}(\phi_A)\bigr).$$
--
--   Alice's reductions are denoted by the subscript $A$. The orders are fixed before comparing the two endpoint spectra.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 3, Remark 2: exact Renyi-gap communication bound

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

/-- PDF p.3, Remark 2: exact Renyi-gap bound, including orders zero, one, infinity. -/
theorem exact_renyi_gap_lower (phi : EuclideanSpace ℂ (A × B))
    (psi : EuclideanSpace ℂ (C × D)) (hphi : ‖phi‖ = 1) (hpsi : ‖psi‖ = 1)
    (alpha beta : RenyiOrder) (horder : alpha < beta) (cost : ℝ)
    (hprotocol : Quantum (pureDensity phi) (pureDensity psi) cost) :
    cost ≥ (renyiGap (aliceDensity psi) alpha beta -
      renyiGap (aliceDensity phi) alpha beta) / 2 := by sorry

end Operational

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
