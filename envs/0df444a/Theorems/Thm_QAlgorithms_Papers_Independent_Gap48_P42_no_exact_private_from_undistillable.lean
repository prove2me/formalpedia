-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P42_no_exact_private_from_undistillable
-- name    : QAlgorithms.Papers.Independent.Gap48.P42.no_exact_private_from_undistillable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:41:17.044573+00:00
-- url     : https://prove2.me/theorems/4c1bd568-5b67-4cbb-a3b8-c8dcca92566c
-- title:
--   Undistillable states cannot yield exact private dits even by successful filtering
-- statement:
--   Let $\rho$ be any normalized finite bipartite density operator on positive local dimensions, and suppose its asymptotic Bell-pair distillable entanglement is zero. For every positive integer $n$, every $d\ge2$, every pair of positive finite shield dimensions, every normalized shield density $\tau$, and every family of joint-shield unitaries, form the corresponding exact private state $\gamma^{(d)}$. Then
--
--   $$
--   \nexists\ \text{complete adaptive LOCC protocol on }\rho^{\otimes n}
--   \text{ with a positive-probability outcome equal to }\gamma^{(d)}.
--   $$
--
--   Each owner retains its own shield, and local ancillas, disposal and arbitrary two-way classical messages are allowed. The conclusion includes deterministic conversion as a special case. It rules out exact finite private targets, while allowing nonzero asymptotic key and approximation by private states with growing shields.
-- source:
--   Quantum states representing perfectly secure bits are always distillable, arXiv:quant-ph/0602176v2, PDF p. 4, IV, unnumbered consequence

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42

namespace QAlgorithms.Papers.Independent.Gap48.P42

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, IV: an undistillable state cannot yield an exact finite private
dit of nontrivial key dimension, even on a positive-probability branch from
any positive finite number of copies. This asserts neither zero asymptotic
key nor a uniform distance from private states with growing shields. -/
theorem no_exact_private_from_undistillable {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hrho : IsDensityMatrix rho)
    (hzero : bipartiteDistillable rho = 0) :
    ∀ n : ℕ, 0 < n → ∀ d s t : ℕ, 2 ≤ d → 0 < s → 0 < t →
    ∀ tau : Matrix (Fin s × Fin t) (Fin s × Fin t) ℂ, IsDensityMatrix tau →
    ∀ U : Fin d → Matrix.unitaryGroup (Fin s × Fin t) ℂ,
      ¬ CanSelect ![a ^ n, b ^ n] ![d * s, d * t]
        (asTwoParties (Dependency50.P42.dimensionedPower rho n))
        (asTwoParties (bipartitePrivate tau U)) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P42
