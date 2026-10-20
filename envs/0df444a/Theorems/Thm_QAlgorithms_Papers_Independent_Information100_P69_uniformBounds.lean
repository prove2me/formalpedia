-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_uniformBounds
-- name    : QAlgorithms.Papers.Independent.Information100.P69.uniformBounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:54:27.367412+00:00
-- url     : https://prove2.me/theorems/c8d6a44c-de30-4163-9abf-6599a3a855ce
-- title:
--   Uniform entropy/testing bounds and weak converse
-- statement:
--   Under F1–F3, put $C=\log_2\dim B-\log_2\lambda_{\min}(\omega)$. For every positive blocklength $n$ and $0<\varepsilon<1$, the optimized entropy $E_n$ and composite testing coefficient $\beta_{\varepsilon,n}$ satisfy
--   $$0\le E_n\le nC,\qquad(1-\varepsilon)2^{-nC}\le\beta_{\varepsilon,n}\le1-\varepsilon,\qquad(1-\varepsilon)(-\log_2\beta_{\varepsilon,n})\le E_n+1.$$
--   In particular the entropy is finite and the testing coefficient is positive. These are uniform bounds and a weak converse.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 8, Lemma 4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Lemma 4, all three finite-block bounds (6)–(8), PDF pp.8–9. -/
theorem uniformBounds [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) (F : BlockFamily A B)
    (omega : Matrix B B ℂ) (hF : Admissible F omega) (n : ℕ) (hn : 1 ≤ n)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    let E := resourceEntropy (power N n) (F n)
    let b := beta (power N n) (F n) eps
    (0 ≤ E ∧ E ≤ ENNReal.ofReal ((n:ℝ)*capacity omega)) ∧
    ((1-eps)*Real.rpow 2 (-(n:ℝ)*capacity omega) ≤ b ∧ b ≤ 1-eps) ∧
    ENNReal.ofReal ((1-eps)*(-Real.logb 2 b)) ≤ E+1 := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
