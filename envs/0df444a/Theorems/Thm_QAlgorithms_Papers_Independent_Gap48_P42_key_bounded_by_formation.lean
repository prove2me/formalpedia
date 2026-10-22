-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P42_key_bounded_by_formation
-- name    : QAlgorithms.Papers.Independent.Gap48.P42.key_bounded_by_formation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:40:39.024679+00:00
-- url     : https://prove2.me/theorems/377c22e7-3e29-4773-9b87-1366fe00e7b7
-- title:
--   Distillable key is bounded by entanglement of formation
-- statement:
--   Let $a,b$ be positive finite dimensions and let $\rho$ be any positive semidefinite trace-one operator on $\mathbb C^a\otimes\mathbb C^b$. Define $K_D(\rho)$ as the supremum of nonnegative achievable private-key rates under trace-preserving adaptive LOCC. An achievable rate uses positive input block lengths $n$, complete outputs approximating exact private states $\gamma^{(d_n)}$ in full trace norm with error tending to zero, and asymptotic lower rate $\liminf_n n^{-1}\log_2d_n$. Every positive finite shield dimension and every joint-shield twist is permitted at each $n$; shields have no growth restriction. Rates and entropies use bits.
--
--   Let $E_F$ be the convex roof of the Alice marginal entropy over all finite normalized pure ensembles realizing $\rho$. Then
--
--   $$
--   K_D(\rho)\le E_F(\rho).
--   $$
--
--   This includes zero key and gives a single-copy upper bound for the asymptotic key resource. The finite real formation value is embedded in the extended nonnegative reals for the comparison.
-- source:
--   Quantum states representing perfectly secure bits are always distillable, arXiv:quant-ph/0602176v2, PDF p. 4, III, consequence immediately after Property 2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42

namespace QAlgorithms.Papers.Independent.Gap48.P42

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, immediately after Property 2: K_D<=E_F for every bipartite
state, with the actual normalized pure-ensemble convex roof. -/
theorem key_bounded_by_formation {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hrho : IsDensityMatrix rho) :
    distillableKey rho ≤ ENNReal.ofReal (Information100.P08.formation rho) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P42
