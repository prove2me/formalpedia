-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P76_amplifiedGramCompletion
-- name    : QAlgorithms.Papers.Independent.Information100.P76.amplifiedGramCompletion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:00:44.390288+00:00
-- url     : https://prove2.me/theorems/14a260c4-8007-46b1-89ec-4a3b7a1bc230
-- title:
--   Lemma 4.2: amplified Gram completion in the target Kraus span
-- statement:
--   Let $(A_a)_{a=1}^k$ be a fixed minimal normalized Kraus family for a CPTP map on $\mathbb C^q$, where $q,k\ge1$. Put $\mathcal K=\operatorname{span}\{A_a\}$, $\mathcal D=\operatorname{span}\{A_a^*A_b\}$, and $L(E_{ab})=A_a^*A_b$. Then $L(I_k)=I_q$. There is a complex-linear, Hermiticity-preserving right inverse $R$ on $\mathcal D$, expressible on the whole matrix space as $R(X)=\sum_\ell\operatorname{Tr}(F_\ell X)C_\ell$ with fixed Hermitian $F_\ell,C_\ell$. For $B=\max(1,\sum_\ell\|F_\ell\|_1\|C_\ell\|_\infty)$,
--
--   $$\|(R\otimes\mathrm{id}_{H_0})(X)\|_\infty\le B\|X\|_\infty$$
--
--   at every positive finite auxiliary dimension. For any $V=\sum_a A_a\otimes B_a$ on $\mathbb C^q\otimes H_0$ with $\Delta=V^*V-I$ and $\|\Delta\|_\infty\le d$, $d\ge0$, set $t=Bd$. There are coefficients $C_a:H_0\to\mathbb C^k\otimes H_0$ giving $W=\sum_a A_a\otimes C_a$ with
--
--   $$W^*W=\frac{tI-\Delta}{1+t},\qquad\frac{V^*V}{1+t}+W^*W=I,\qquad\|W\|_\infty\le\sqrt{\frac{t+d}{1+t}}.$$
--
--   Thus stacking $V/\sqrt{1+t}$ and $W$ completes the almost-isometry within the prescribed Kraus span, uniformly in $H_0$. Positivity of the right inverse is not asserted.
-- source:
--   Bath dimension and initial entropy for closed repeated use of a quantum channel, arXiv:2609.18267v1, PDF p. 7, Lemma 4.2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P76

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P76

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open Filter

/-- PDF p.7, Lemma 4.2: a Hermiticity-preserving right inverse with a uniform trace-slice
bound, and an almost-isometry completion inside the fixed Kraus span. The right inverse is
a conclusion, is not assumed positive, and the output auxiliary space is k tensor H0. -/
theorem amplifiedGramCompletion {q k : ℕ} (hq : 0 < q) (hk : 0 < k)
    (A : Fin k → Op q) (hA : IsKrausFamily A) (hminimal : LinearIndependent ℂ A) :
    gramMap A 1 = 1 ∧
    ∃ R : Op q →ₗ[ℂ] Op k, ∃ ell : ℕ, ∃ F : Fin ell → Op q, ∃ C : Fin ell → Op k,
      (∀ j, (F j).IsHermitian ∧ (C j).IsHermitian) ∧
      (∀ X : Op q, R X = ∑ j, (F j * X).trace • C j) ∧
      (∀ X : Op q, X ∈ gramSpace A → gramMap A (R X) = X) ∧
      (∀ X : Op q, X.IsHermitian → (R X).IsHermitian) ∧
      let B := max 1 (∑ j, traceNorm (F j) * ‖C j‖)
      (∀ d : ℕ, 0 < d → ∀ X : Matrix (Fin q × Fin d) (Fin q × Fin d) ℂ,
        ‖amplify R X‖ ≤ B * ‖X‖) ∧
      (∀ d : ℕ, 0 < d → ∀ delta : ℝ, 0 ≤ delta → ∀ coefficients : Fin k → Op d,
        let V := spanMap A coefficients
        let defect := Vᴴ * V - 1;
        ‖defect‖ ≤ delta →
          ∃ correction : Fin k → Matrix (Fin k × Fin d) (Fin d) ℂ,
            let W := spanMap A correction
            let t := B * delta
            Wᴴ * W = ((1 / (1 + t) : ℝ) : ℂ) • (t • (1 : Matrix
              (Fin q × Fin d) (Fin q × Fin d) ℂ) - defect) ∧
            ((1 / (1 + t) : ℝ) : ℂ) • (Vᴴ * V) + Wᴴ * W = 1 ∧
            ‖W‖ ≤ Real.sqrt ((t + delta) / (1 + t))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P76

end
