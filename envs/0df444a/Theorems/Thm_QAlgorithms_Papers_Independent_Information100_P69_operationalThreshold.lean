-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_operationalThreshold
-- name    : QAlgorithms.Papers.Independent.Information100.P69.operationalThreshold
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:00:23.628791+00:00
-- url     : https://prove2.me/theorems/68c29fbb-7b41-4456-987d-cedc5fac22a9
-- title:
--   Operational threshold
-- statement:
--   Under F1–F3, there are uniform parallel testers whose target acceptance $p_n$ and worst-case free acceptance $q_n>0$ satisfy
--   $$p_n\to1,\qquad-\frac1n\log_2q_n\to R_{\mathcal F}(\mathcal N).$$
--   Conversely, for every $r>R_{\mathcal F}(\mathcal N)$ there are $K_r,c_r>0$, independent of the tester and its reference, such that every parallel tester and every positive blocklength satisfy
--   $$q_n\le2^{-nr}\ \Longrightarrow\ p_n\le K_r2^{-c_rn}.$$
--   This gives achievability and an exponential strong converse, with a prefactor covering all lengths.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 18, Theorem 12

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Theorem 12, achievability and exponential strong converse uniform in references, PDF p.18. -/
theorem operationalThreshold [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) (F : BlockFamily A B)
    (omega : Matrix B B ℂ) (hF : Admissible F omega) :
    (∃ t : (n : ℕ) → Tester (Sites A n) (Sites A n) (Sites B n),
      (∀ n, 1 ≤ n → 0 < worst (t n) (F n)) ∧
      Tendsto (fun j : ℕ => acceptance (t (j+1)) (power N (j+1))) atTop (nhds 1) ∧
      Tendsto (fun j : ℕ => -Real.logb 2 (worst (t (j+1)) (F (j+1)))/(j+1)) atTop (nhds (rate N F))) ∧
    (∀ r : ℝ, rate N F < r → ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
      ∀ n, 1 ≤ n → ∀ d : ℕ, ∀ t : Tester (Fin d) (Sites A n) (Sites B n),
        worst t (F n) ≤ Real.rpow 2 (-(n:ℝ)*r) →
          acceptance t (power N n) ≤ K*Real.rpow 2 (-c*n)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
