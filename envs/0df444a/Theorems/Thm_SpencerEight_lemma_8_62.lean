-- Prove2me | Theorems.Thm_SpencerEight_lemma_8_62
-- name    : SpencerEight.lemma_8_62
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:42.87342+00:00
-- url     : https://prove2.me/theorems/ba48c242-0d5e-432c-b943-043a7f92970a
-- title:
--   Lemma 8.62 — hereditary joint first residual row
-- statement:
--   Suppose $B_i=T^{1/2}A_iT^{1/2}$, $0\preceq T\preceq I$, and all $A_i$ are real symmetric contractions. Suppose $\operatorname{tr}[T^{2j}]\le n\tau_j$ for $j=3,4$, and put
--   $$e_{\mathrm{joint}}:=0.0003494+0.1605\tau_3+0.4636\tau_4.$$
--   For every $w>0$ and every nonempty subfamily of actual size $m\le wn$,
--   $$\gamma_m\Bigl[\bigl\|\sum_{i=1}^m\xi_iB_i\bigr\|\le\sqrt{wn/0.14}\Bigr]\ge\exp[-me_{\mathrm{joint}}/w].\tag{140}$$
--   There is no rank term and no additional moment-body charge in this row.
--
--   Differences from the source:
--   - reading: tr[T^{2j}] ≤ nτ_j for the available envelope powers, including j = 3, 4 → the hypothesis at exactly j = 3 and j = 4; reason: every reading of the phrase implies these two, and the bound involves only τ₃ and τ₄
--   - encoding: a nonempty subfamily of size m, Gaussian on ℝ^m → a nonempty Finset S with m = |S|, Gaussian on S → ℝ; reason: the same object
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.62, p.125 (PDF p.125)

import Mathlib
import Definitions.Def_SpencerEight_IsSymmContraction
import Definitions.Def_SpencerEight_gammaM
import Definitions.Def_SpencerEight_sqrtM
open scoped Matrix.Norms.L2Operator

namespace SpencerEight

/-- Lemma 8.62 (Hereditary joint first residual row), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.125 (PDF p.125), Eq. (140).

**Formalization Note** The envelope hypothesis "for the available envelope powers, including `j = 3, 4`" is taken at exactly `j = 3` and `j = 4`, which every reading of the phrase implies; the bound involves only `τ₃, τ₄`. A subfamily is a nonempty `S`, with the Gaussian on `ℝ^S`, `m = |S|`. -/
theorem lemma_8_62 {n : ℕ} {ι : Type*} [Fintype ι] (T : Matrix (Fin n) (Fin n) ℝ)
    (hT : T.PosSemidef) (hT1 : (1 - T).PosSemidef) (A : ι → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, IsSymmContraction (A i)) {τ₃ τ₄ : ℝ} (hτ₃ : (T ^ 6).trace ≤ n * τ₃)
    (hτ₄ : (T ^ 8).trace ≤ n * τ₄) {w : ℝ} (hw : 0 < w) (S : Finset ι) (hS : S.Nonempty)
    (hm : (S.card : ℝ) ≤ w * n) :
    ENNReal.ofReal (Real.exp (-((S.card : ℝ) * (0.0003494 + 0.1605 * τ₃ + 0.4636 * τ₄) / w))) ≤
      gammaM S {ξ | ‖∑ i : S, ξ i • (sqrtM T * A i * sqrtM T)‖ ≤ Real.sqrt (w * n / 0.14)} := by sorry

end SpencerEight
