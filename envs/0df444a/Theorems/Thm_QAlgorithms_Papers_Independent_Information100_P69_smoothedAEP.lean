-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_smoothedAEP
-- name    : QAlgorithms.Papers.Independent.Information100.P69.smoothedAEP
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:59:44.684725+00:00
-- url     : https://prove2.me/theorems/979a1150-b38a-4764-a944-dc75098d3dd1
-- title:
--   CPTP-smoothed resource AEP
-- statement:
--   Under F1–F3, let $Z_n^\delta$ be the infimum of $\log_2\lambda$ over CPTP approximations $L$ with full diamond distance at most $\delta$ from $\mathcal N^{\otimes n}$ and free dominators $S\in\mathcal F_n$ satisfying $L\le_{\rm CP}\lambda S$, $\lambda\ge1$. Suppose $0<\delta_n\le\bar\delta<2$ and $\log_2(1/\delta_n)/n\to0$. Then
--   $$\lim_{n\to\infty}\frac{Z_n^{\delta_n}}n=R_{\mathcal F}(\mathcal N).$$
--   The signed logarithm condition includes fixed radii above one. This is an AEP with trace-preserving smoothing and optimized free dominators.
--
--   The testing model uses one normalized pure input, possibly entangled across uses and with a reference, and one acceptance effect shared by every alternative. The symbol $\le_{\rm CP}$ means that the difference of the larger and smaller maps is completely positive; $\|\cdot\|_\diamond$ is the full diamond norm. Information quantities use base-2 logarithms.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 17, Theorem 11

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Theorem 11, CPTP-smoothed resource AEP at every subexponential radius, PDF pp.17–18. -/
theorem smoothedAEP [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) (F : BlockFamily A B)
    (omega : Matrix B B ℂ) (hF : Admissible F omega) (delta : ℕ → ℝ) (bar : ℝ)
    (hdelta : ∀ n, 1 ≤ n → 0 < delta n ∧ delta n ≤ bar) (hbar : bar < 2)
    (hsubexp : Tendsto (fun j : ℕ => Real.logb 2 (1/delta (j+1))/(j+1)) atTop (nhds 0)) :
    Tendsto (fun j : ℕ => smoothCost (power N (j+1)) (F (j+1)) (delta (j+1)) / (j+1))
      atTop (nhds (ENNReal.ofReal (rate N F))) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
