-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_renyi_canIncrease
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.renyi_canIncrease
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:32:06.507664+00:00
-- url     : https://prove2.me/theorems/d06046e9-bcfc-4448-aafa-d307b8562e31
-- title:
--   Corollary 3: strict Renyi entropy increase below one half
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. A non-entangling map is completely positive and preserves the full separable positive cone. A channel is also trace preserving. For every $0\le\alpha<1/2$, there exist bipartite pure states $\psi,\varphi$ and a non-entangling channel $\Lambda$ between their registers such that
--
--   $$\Lambda(\psi)=\varphi,\qquad E_\alpha(\varphi)>E_\alpha(\psi).$$
--
--   Here $E_\alpha$ is the base-two Renyi entropy of the squared Schmidt coefficients; $E_0$ is the logarithm of Schmidt rank.
--
--   This is deterministic pure-to-pure nonmonotonicity.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 9, Corollary 3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P19

noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P19

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P19 (Bip)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

/-- Corollary 3, PDF pp.9-10: deterministic pure-state Renyi nonmonotonicity
below one half. No average or stochastic interpretation is asserted. -/
theorem renyi_canIncrease (alpha : ℝ) (h0 : 0 ≤ alpha) (hhalf : alpha < 1 / 2) :
    ∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      ∃ psi : UnitBipartiteKet a b, ∃ phi : UnitBipartiteKet c d,
      ∃ L : Superop (Fin a × Fin b) (Fin c × Fin d),
        IsChannel L ∧ NE L ∧ L psi.rho = phi.rho ∧
        schmidtRenyi (ENNReal.ofReal alpha) psi.ket < schmidtRenyi (ENNReal.ofReal alpha) phi.ket := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
