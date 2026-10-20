-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_isometricCompletion
-- name    : QAlgorithms.Papers.Independent.Information100.P69.isometricCompletion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:11:15.026566+00:00
-- url     : https://prove2.me/theorems/2ee6c1d3-7131-48de-b42d-720551dcf3ac
-- title:
--   Completion for an isometric target
-- statement:
--   Fix local dimensions $a,d$ with $a\mid d$, positive witness minimum eigenvalues $t,w$, and $c>0$. There is a finite $K_c\ge0$, uniform over isometries, families, blocklengths, accuracies, and branch data, with the following property. For any family satisfying F1–F5 and any isometry $J:A\to D$, suppose at $n\ge1$ that $M\in\mathcal F_n$, $0<p\le1$, $M\ge_{\rm CP}p\operatorname{Ad}_V$, $\|V\|_\infty\le1$, and $\operatorname{Re}((J^{\otimes n})^\dagger V)\ge cI$. For every $0<\delta\le1/16$, there are free $S_n$ and CPTP $L_n$ with
--   $$p2^{-K_cn^{2/3}\log_2((n+1)/\delta)}L_n\le_{\rm CP}S_n,\quad\|L_n-\operatorname{Ad}_{J^{\otimes n}}\|_\diamond\le\delta.$$
--   This completes a positive-overlap branch for every length and accuracy, retaining divisibility and without imposing the derived restriction $c\le1$.
--
--   The testing model uses one normalized pure input, possibly entangled across uses and with a reference, and one acceptance effect shared by every alternative. The symbol $\le_{\rm CP}$ means that the difference of the larger and smaller maps is completely positive; $\|\cdot\|_\diamond$ is the full diamond norm. Information quantities use base-2 logarithms.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 34, Proposition 30

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Proposition 30, isometric completion including complementary regimes; divisibility is
retained and the constant precedes J, F, p, V, n and delta; PDF pp.34–37. -/
theorem isometricCompletion [Nonempty A] [Nonempty B] (t w c : ℝ) (ht : 0 < t) (hw : 0 < w) (hc : 0 < c)
    (hdiv : Fintype.card A ∣ Fintype.card B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ tau : Matrix A A ℂ, ∀ omega : Matrix B B ℂ,
      minPositiveEigenvalue tau = t → minPositiveEigenvalue omega = w →
      ∀ F : BlockFamily A B, Admissible F omega → Additional F tau →
      ∀ J : Matrix B A ℂ, J.conjTranspose*J = 1 →
      ∀ n, 1 ≤ n → ∀ M ∈ F n, ∀ p : ℝ, 0 < p → p ≤ 1 →
      ∀ V : Matrix (Sites B n) (Sites A n) ℂ, CPLe ((p:ℂ) • conjSuperop V) M →
        specNorm V ≤ 1 → (hermitianPart ((matrixPower J n).conjTranspose*V)-(c:ℂ) • 1).PosSemidef →
      ∀ delta : ℝ, 0 < delta → delta ≤ 1/16 → ∃ S ∈ F n,
        ∃ L : Superop (Sites A n) (Sites B n), IsChannel L ∧
          CPLe (((p*Real.rpow 2 (-overhead K n delta):ℝ):ℂ) • L) S ∧
          diamond (L-conjSuperop (matrixPower J n)) ≤ delta := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
