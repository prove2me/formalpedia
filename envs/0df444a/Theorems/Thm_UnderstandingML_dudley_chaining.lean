-- Prove2me | Theorems.Thm_UnderstandingML_dudley_chaining
-- name    : UnderstandingML.dudley_chaining
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:49:40.741594+00:00
-- url     : https://prove2.me/theorems/eb06ff7b-1cec-4001-bcd4-71c21ff511ed
-- title:
--   Lemma 27.4 (Dudley's chaining): R(A) ≤ c2^{−M}/√m + (6c/m) ∑_{k=1}^M 2^{−k} √(log N(c2^{−k}, A)) for any enclosing radius c
-- statement:
--   **Lemma 27.4.** Let $c = \min_{\bar a}\max_{a \in A}\|a - \bar a\|$. Then, for any integer $M > 0$,
--   $$R(A) \le \frac{c\,2^{-M}}{\sqrt m} + \frac{6c}{m}\sum_{k=1}^M 2^{-k}\sqrt{\log(N(c\,2^{-k}, A))}.$$
--
--   Formally: for any center $\bar a$ and any $c$ with $\|a - \bar a\| \le c$ on $A$ (the book's minimal $c$ is the special case), $A$ nonempty, $m \ge 1$; covering numbers of the bounded set $A$ are finite.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §27.2 pp. 389-390, Lemma 27.4 with its proof

import Definitions.Def_UnderstandingML_Covering

open MeasureTheory

namespace UnderstandingML

/-- **Lemma 27.4 (Dudley's chaining)** (p. 389). Let `c = min_ā max_{a ∈ A} ‖a − ā‖`. Then, for
any integer `M > 0`,
`R(A) ≤ c 2^{−M}/√m + (6c/m) ∑_{k=1}^M 2^{−k} √(log N(c 2^{−k}, A))`.
Stated for any center `ā` and any `c` with `‖a − ā‖ ≤ c` on `A` (the minimal such `c` is the
book's); `A` nonempty, `m ≥ 1`. -/
theorem dudley_chaining {m : ℕ} (hm : 0 < m) (A : Set (Fin m → ℝ)) (hA : A.Nonempty) (c : ℝ)
    (abar : Fin m → ℝ) (hc : ∀ a ∈ A, eucNorm (a - abar) ≤ c) (M : ℕ) (hM : 0 < M) :
    rademacher A ≤ c * (2 : ℝ)⁻¹ ^ M / Real.sqrt m +
      6 * c / m * ∑ k ∈ Finset.Icc 1 M,
        (2 : ℝ)⁻¹ ^ k * Real.sqrt (Real.log ((coveringNumber (c * (2 : ℝ)⁻¹ ^ k) A).toNat)) := by sorry

end UnderstandingML
