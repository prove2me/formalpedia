-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_maximallyEntangled_conversion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.maximallyEntangled_conversion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:30:47.909192+00:00
-- url     : https://prove2.me/theorems/561670ec-614f-4f38-8b5c-07f73ea7436f
-- title:
--   Theorem 1: exact conversion from maximally entangled currency
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. A non-entangling map is completely positive and preserves the full separable positive cone. A channel is also trace preserving. Let $k\ge2$, let $\phi_k^+$ be the normalized maximally entangled state on $\mathbb C^k\otimes\mathbb C^k$, and let $\psi$ be any bipartite pure output state, on possibly different local dimensions. Write $R(\rho)$ for the standard robustness, minimized over separable normalized noise. Then
--
--   $$\exists\,\Lambda\text{ non-entangling channel}:\Lambda(\phi_k^+)=\psi\quad\Longleftrightarrow\quad R(\psi)\le R(\phi_k^+).$$
--
--   This characterizes exact preparation from maximally entangled currency.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 8, Theorem 1

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

/-- Theorem 1, PDF p.8: exact conversion from maximally entangled currency
is characterized by standard robustness, with arbitrary positive output dimensions. -/
theorem maximallyEntangled_conversion {a b k : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hk : 2 ≤ k) (psi : UnitBipartiteKet a b) :
    (∃ L : Superop (Fin k × Fin k) (Fin a × Fin b),
      IsChannel L ∧ NE L ∧ L (epr k) = psi.rho) ↔
      standardStateRobustness psi.rho ≤ standardStateRobustness (epr k) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
