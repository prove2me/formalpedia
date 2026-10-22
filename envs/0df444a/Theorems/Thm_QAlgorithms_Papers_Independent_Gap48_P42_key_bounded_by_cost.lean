-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P42_key_bounded_by_cost
-- name    : QAlgorithms.Papers.Independent.Gap48.P42.key_bounded_by_cost
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:40:00.400824+00:00
-- url     : https://prove2.me/theorems/61f60671-119f-4367-a4fd-9c1c8d567b7f
-- title:
--   Distillable key is bounded by operational entanglement cost
-- statement:
--   Let $a,b$ be positive finite dimensions and let $\rho$ be any positive semidefinite trace-one operator on $\mathbb C^a\otimes\mathbb C^b$. Define $K_D(\rho)$ as the supremum of nonnegative achievable private-key rates under trace-preserving adaptive LOCC. An achievable rate uses positive input block lengths $n$, complete outputs approximating exact private states $\gamma^{(d_n)}$ in full trace norm with error tending to zero, and asymptotic lower rate $\liminf_n n^{-1}\log_2d_n$. Every positive finite shield dimension and every joint-shield twist is permitted at each $n$; shields have no growth restriction. Rates and entropies use bits.
--
--   Let $E_C(\rho)$ be operational singlet cost with adaptive LOCC and vanishing preparation error. Then
--
--   $$
--   K_D(\rho)\le E_C(\rho).
--   $$
--
--   This includes states with zero distillable key and requires no attained key rate or optimal protocol sequence. It relates two operational resources on an arbitrary bipartite state, which need not itself be private.
--
--   **Formalization Note** The key supremum takes values in the extended nonnegative reals; the finite real cost is embedded in that space.
-- source:
--   Quantum states representing perfectly secure bits are always distillable, arXiv:quant-ph/0602176v2, PDF p. 4, III, Property 2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42

namespace QAlgorithms.Papers.Independent.Gap48.P42

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, Property 2: every finite bipartite density has K_D<=E_C.
No positive-key, attained-rate, shield-growth or continuity hypothesis is added.
The proof's key-dimension-only continuity display is not asserted separately. -/
theorem key_bounded_by_cost {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hrho : IsDensityMatrix rho) :
    distillableKey rho ≤ ENNReal.ofReal
      (Dependency50.P42.entanglementCost Dependency50.P42.paperBures rho) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P42
