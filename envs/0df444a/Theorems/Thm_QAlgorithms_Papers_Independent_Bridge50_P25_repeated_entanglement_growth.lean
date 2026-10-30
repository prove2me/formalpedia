-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P25_repeated_entanglement_growth
-- name    : QAlgorithms.Papers.Independent.Bridge50.P25.repeated_entanglement_growth
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:05:21.953786+00:00
-- url     : https://prove2.me/theorems/cea38ca2-4d5b-428b-b344-dd4841779a81
-- title:
--   Corollary III.1: m-use entanglement growth
-- statement:
--   Let $T$ be a quantum channel between positive finite-dimensional input and output systems, let $m\ge1$ be an integer, and let $\alpha>1$ be finite. Start with any normalized state $\rho_{A_1A'B_1}$, send $A'$ through $T$, and interleave exactly $m$ actual channel applications with arbitrary two-party LOCC and positive finite changing local workspaces. Let $\phi_{\widetilde A\widetilde B}$ be the resulting state after the last LOCC. Then
--
--   $$E_\alpha^{\widetilde A:\widetilde B}(\phi)\le mE_{\max}(T)+E_\alpha^{A_1A':B_1}(\rho).$$
--
--   All entropies use bits, and $E_\alpha$ minimizes sandwiched divergence to separable states on its indicated cut. The initial state may already be entangled.
--
--   This records accumulation over the actual channel-use recursion, including the first application before any interleaving.
-- source:
--   Relative Entropy Bounds on Quantum, Private and Repeater Capacities, arXiv:1604.03448v2, PDF p. 12, Corollary III.1

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P25

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (eMax)

variable {I J A B C D : Type}

variable [Fintype I] [DecidableEq I] [Nonempty I]

variable [Fintype J] [DecidableEq J] [Nonempty J]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

/-- Corollary III.1, PDF p.12: m>=1, exactly m channel uses, arbitrary initial
state. Correct the printed intermediate output to B_(i+1) and range to i<m,
following Definition II.3 on p.6; the protocol recursion keeps the first T. -/
theorem repeated_entanglement_growth (T : Superop I J) (hT : IsChannel T)
    (m a b : ℕ) (hm : 0 < m)
    (P : Superop ((Fin (a + 1) × I) × Fin (b + 1)) (C × D))
    (hP : TwoWayChannelProtocol T C D m a b P) (alpha : ℝ) (halpha : 1 < alpha)
    (rho : Mat ((Fin (a + 1) × I) × Fin (b + 1))) (hrho : IsDensityMatrix rho) :
    entanglementRenyi alpha (P rho) ≤
      (m : EReal) * channelEMax T + entanglementRenyi alpha rho := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P25

end
