-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_zero_communication_conversion
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.zero_communication_conversion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:07:26.91089+00:00
-- url     : https://prove2.me/theorems/ae652f65-f0b3-42db-a6e0-310a22fc9463
-- title:
--   Remark 3: exact zero-communication conversion of maximally entangled states
-- statement:
--   For normalized finite-dimensional bipartite pure states $\phi,\psi$, write $r_\phi,r_\psi$ for their positive Schmidt ranks, and $\Delta^{\alpha\beta}=S_\alpha-S_\beta$ for base-two Rényi gaps. Any exact deterministic zero-communication conversion obeys $\Delta^{\alpha\beta}(\psi_A)\le\Delta^{\alpha\beta}(\phi_A)$ for every $0\le\alpha<\beta\le\infty$. Moreover, if $\phi_A$ is flat on its positive support, then
--
--   $$\phi\longrightarrow\psi\text{ with zero communication}\quad\iff\quad \psi_A\text{ is flat and }r_\psi\mid r_\phi.$$
--
--   Local ancillas and disposal are allowed. This characterizes the exact zero-communication conversions between maximally entangled states, including product targets.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 3, Remark 3: exact zero-communication conversion of maximally entangled states

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

/-- PDF p.3, Remark 3: every Renyi gap is nonincreasing at zero communication;
from a flat input, the flat target's positive Schmidt rank must and may divide the input rank. -/
theorem zero_communication_conversion (phi : EuclideanSpace ℂ (A × B))
    (psi : EuclideanSpace ℂ (C × D)) (hphi : ‖phi‖ = 1) (hpsi : ‖psi‖ = 1) :
    (Quantum (pureDensity phi) (pureDensity psi) 0 →
      ∀ alpha beta : RenyiOrder, alpha < beta →
        renyiGap (aliceDensity psi) alpha beta ≤ renyiGap (aliceDensity phi) alpha beta) ∧
    (Flat (aliceDensity phi) →
      (Quantum (pureDensity phi) (pureDensity psi) 0 ↔
        Flat (aliceDensity psi) ∧ supportRank (aliceDensity psi) ∣ supportRank (aliceDensity phi))) := by sorry

end Operational

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
