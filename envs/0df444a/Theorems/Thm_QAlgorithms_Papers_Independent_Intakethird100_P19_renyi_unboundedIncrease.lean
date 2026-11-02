-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_renyi_unboundedIncrease
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.renyi_unboundedIncrease
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:48:32.200385+00:00
-- url     : https://prove2.me/theorems/4134d91e-890b-489f-a33e-140a0ea024ee
-- title:
--   Unbounded Renyi entropy increase below one half
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. A non-entangling map is completely positive and preserves the full separable positive cone. A channel is also trace preserving. For each $0\le\alpha<1/2$ and each real $M>0$, there are finite bipartite pure states $\psi,\varphi$ and a non-entangling channel $\Lambda$ such that
--
--   $$\Lambda(\psi)=\varphi,\qquad E_\alpha(\varphi)-E_\alpha(\psi)>M.$$
--
--   All entropies are in bits; the dimensions may depend on $\alpha$ and $M$.
--
--   This states the introductory claim in its stronger unbounded form.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 3, unbounded-renyi-increase

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

/-- PDF p.3, strengthened introductory claim: arbitrarily large entropy
increases below one half. Dimensions may depend on alpha and the desired increase. -/
theorem renyi_unboundedIncrease (alpha : ℝ) (h0 : 0 ≤ alpha) (hhalf : alpha < 1 / 2)
    (M : ℝ) (hM : 0 < M) :
    ∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      ∃ psi : UnitBipartiteKet a b, ∃ phi : UnitBipartiteKet c d,
      ∃ L : Superop (Fin a × Fin b) (Fin c × Fin d),
        IsChannel L ∧ NE L ∧ L psi.rho = phi.rho ∧
        M < schmidtRenyi (ENNReal.ofReal alpha) phi.ket - schmidtRenyi (ENNReal.ofReal alpha) psi.ket := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
