-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_isometricSmoothing
-- name    : QAlgorithms.Papers.Independent.Information100.P69.isometricSmoothing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:06:44.752832+00:00
-- url     : https://prove2.me/theorems/e87eb17c-19a7-45ee-9485-a68f36653a34
-- title:
--   Exact smoothed isometric benchmark
-- statement:
--   Let $J:A\to B$ be an isometry, let the free alternatives be either all EB or all PPT block channels, and put $a=\dim A$. For every positive blocklength $n$ and full diamond radius $0\le\delta\le2$,
--   $$Z_n^\delta=\log_2\max\{1,a^n(1-\delta/2)\}.$$
--   The dominator is optimized over the entire free family. This gives the exact trace-preserving smoothing cost, including $\delta=0$, $\delta=2$, and $a=1$.
--
--   Here $Z_n^\delta$ is the minimum logarithmic CP-domination cost over CPTP approximations within diamond radius $\delta$ and over all free dominators at blocklength $n$.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 23, Corollary 23

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Corollary 23, exact optimized smoothing including both endpoints, PDF pp.23–24. -/
theorem isometricSmoothing [Nonempty A] [Nonempty B] (J : Matrix B A ℂ) (hJ : J.conjTranspose*J = 1)
    (F : BlockFamily A B) (hF : F ∈ ({ebFamily, pptFamily} : Set (BlockFamily A B)))
    (n : ℕ) (hn : 1 ≤ n) (delta : ℝ) (hdelta : 0 ≤ delta) (hdelta2 : delta ≤ 2) :
    smoothCost (power (conjSuperop J) n) (F n) delta =
      ENNReal.ofReal (Real.logb 2 (max 1 ((Fintype.card A:ℝ)^n*(1-delta/2)))) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
