-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_symmetricEntropyEstimate
-- name    : QAlgorithms.Papers.Independent.Information100.P69.symmetricEntropyEstimate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:12:34.696395+00:00
-- url     : https://prove2.me/theorems/f17caeb1-e87c-4769-9240-934053345e94
-- title:
--   Symmetric finite-block entropy estimate
-- statement:
--   Assume F1–F3 and permutation closure F4, with $C=\log_2 b-\log_2\lambda_{\min}(\omega)$. Put $h=ab$ and $v_n=\binom{n+h^2-1}{h^2-1}$. For $n\ge1$ and $0<\varepsilon<1$, the optimized entropy is finite and
--   $$-\log_2\beta_{\varepsilon,n}\ge\frac{E_n-(1-\varepsilon)(nC+1)-\log_2v_n}{\varepsilon}-1.$$
--   The Lean statement uses the algebraically equivalent upper bound on finite $E_n$. This is the symmetric finite-block entropy/testing comparison; F5 is not assumed.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 39, Lemma 33

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Lemma 33, binomial spectral count and the full symmetric entropy bound, PDF pp.39–40. -/
theorem symmetricEntropyEstimate [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) (F : BlockFamily A B)
    (omega : Matrix B B ℂ) (hF : Admissible F omega) (hperm : PermutationClosed F)
    (n : ℕ) (hn : 1 ≤ n) (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    let h := Fintype.card A*Fintype.card B
    let v := Nat.choose (n+h^2-1) (h^2-1)
    resourceEntropy (power N n) (F n) < ⊤ ∧
    (resourceEntropy (power N n) (F n)).toReal ≤
      eps*(exponent (power N n) (F n) eps+1)+(1-eps)*((n:ℝ)*capacity omega+1)+Real.logb 2 v := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
