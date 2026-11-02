-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_renyi_monotone_pure
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.renyi_monotone_pure
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:33:26.745222+00:00
-- url     : https://prove2.me/theorems/b0cfd89e-40d9-412a-aa82-b8a1e1bc21c7
-- title:
--   Corollary 5: Renyi monotonicity from one half through infinity
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. A non-entangling map is completely positive and preserves the full separable positive cone. A channel is also trace preserving. For every $\alpha\in[1/2,+\infty]$, every pure input $\psi$, every pure output $\varphi$, and every non-entangling channel satisfying $\Lambda(\psi)=\varphi$,
--
--   $$E_\alpha(\varphi)\le E_\alpha(\psi).$$
--
--   The entropies use squared Schmidt coefficients and base-two logarithms, with the Shannon and min-entropy endpoint branches.
--
--   This constrains deterministic pure-state conversions.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 10, Corollary 5

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

/-- Corollary 5, PDF p.10: deterministic pure-to-pure monotonicity,
including infinite order and the endpoint one half. -/
theorem renyi_monotone_pure {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (alpha : RenyiOrder) (hhalf : (1 / 2 : ℝ≥0∞) ≤ alpha)
    (psi : UnitBipartiteKet a b) (phi : UnitBipartiteKet c d)
    (L : Superop (Fin a × Fin b) (Fin c × Fin d))
    (hL : IsChannel L) (hne : NE L) (hconvert : L psi.rho = phi.rho) :
    schmidtRenyi alpha phi.ket ≤ schmidtRenyi alpha psi.ket := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
