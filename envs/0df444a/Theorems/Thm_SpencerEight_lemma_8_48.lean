-- Prove2me | Theorems.Thm_SpencerEight_lemma_8_48
-- name    : SpencerEight.lemma_8_48
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:55.384018+00:00
-- url     : https://prove2.me/theorems/53e43047-6481-4337-8fe1-5ab6ee84e19a
-- title:
--   Lemma 8.48 — a hereditary iterated envelope
-- statement:
--   Suppose $B_i=T^{1/2}A_iT^{1/2}$, where $0\preceq T\preceq I$, each $A_i$ is a real symmetric contraction, and $\operatorname{tr}[T^{2j}]\le n\tau_j$ for every integer $j\ge1$. Let $\|M\|\le L\sqrt n$, $0<L<C$, and put $g:=C-L$, $H:=C\sqrt nI-|M|$, $K:=g\sqrt nH^{-1}$, $T':=K^{1/2}TK^{1/2}$.
--
--   1. For every remaining index, $D_i:=K^{1/2}B_iK^{1/2}=(T')^{1/2}A_i'(T')^{1/2}$ with $0\preceq T'\preceq I$, where all $A_i'$ are symmetric contractions.
--   2. For an integer $k\ge1$, let $p_k(u):=\sum_{j=0}^{d_k}a_{k,j}u^{2j}$ have nonnegative coefficients and satisfy
--   $$(C-Lu)^{2k}p_k(u)\ge(C-L)^{2k}\quad(0\le u\le1).\tag{123}$$
--   If $\operatorname{tr}[p_k(|M|/(L\sqrt n))-a_{k,0}I]\le(1+\delta_{\mathrm{mom}})n\mu_k$, then
--   $$\operatorname{tr}[(T')^{2k}]\le n\bigl(a_{k,0}\tau_k+(1+\delta_{\mathrm{mom}})\mu_k\bigr).\tag{124}$$
--   3. When $d_k\ge1$, the same conclusion holds if instead the weighted statistic $F_k(X):=a_{k,1}\operatorname{tr}[T^{2k}X^2]+\sum_{j=2}^{d_k}a_{k,j}\operatorname{tr}[X^{2j}]$ at $X:=|M|/(L\sqrt n)$ is at most $(1+\delta_{\mathrm{mom}})n\mu_k$.
--   4. For a Gaussian series $G:=\sum_{i=1}^m\xi_iB_i$ with $m\le wn$ and $L^2s_+^2\eta\ge w$, put $X:=G/(s_+L\sqrt n)$. The statistics $\operatorname{tr}[p_k(X)-a_{k,0}I]$ and $F_k(X)$ are nonnegative, even and convex functions of $\xi$, and their expectations are at most $n\mu_k$ for the respective choices
--   $$\mu_k:=\sum_{j=1}^{d_k}a_{k,j}\mathrm{df}(j)\eta^j\tau_j,\qquad\mu_k:=a_{k,1}\eta\tau_{k+1}+\sum_{j=2}^{d_k}a_{k,j}\mathrm{df}(j)\eta^j\tau_j.$$
--
--   All these assertions hold for a skipped phase with $M=0$. The lemma keeps one common envelope through each congruence.
--
--   Differences from the source:
--   - generalization: M a partial sum → any symmetric M with ‖M‖ ≤ L√n, which includes the skipped phase M = 0; reason: the page's proof uses only these properties; a partial sum is such a matrix
--   - encoding: n the dimension, with division by L√n → 0 < n; reason: a nondegeneracy condition: it excludes only the division by zero
--   - encoding: expectations of the statistics → Integrable together with a Bochner integral bound; reason: the statistics are polynomial in ξ, and the integrability is stated so that the integral is not a junk value
--   - encoding: nonnegative coefficients a_{k,0}, …, a_{k,d_k} → a : ℕ → ℝ nonnegative at every index; reason: values beyond d_k are not used
--   - generalization: the Gaussian-series clause for the p_k satisfying (123) → the Gaussian-series clause for every p_k with nonnegative coefficients, (123) not assumed; reason: nonnegativity, evenness, convexity and the two expectation bounds use only a_{k,j} ≥ 0, m ≤ wn, L²s₊²η ≥ w and the envelope; the source's p_k are instances
--   - encoding: a Gaussian series G := Σ_{i=1}^m ξ_iB_i over the remaining indices, m ≤ wn → the series over all of the finite index type ι, with |ι| ≤ wn; reason: ι is arbitrary, so every subfamily is an instance
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.48, p.108 (PDF p.108)

import Mathlib
import Definitions.Def_SpencerEight_IsSymmContraction
import Definitions.Def_SpencerEight_gammaM
import Definitions.Def_SpencerEight_signedSum
import Definitions.Def_SpencerEight_absM
import Definitions.Def_SpencerEight_sqrtM
import Definitions.Def_SpencerEight_evenPoly
import Definitions.Def_SpencerEight_weightedStat
import Definitions.Def_SpencerEight_sPlus
import Definitions.Def_SpencerEight_deltaMom
import Definitions.Def_SpencerEight_df
open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace SpencerEight

/-- Lemma 8.48 (A hereditary iterated envelope), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.108 (PDF p.108). All clauses: the common representation, with one `T′` for every index; Eq. (124) under the unweighted moment hypothesis and, when `d_k ≥ 1`, under the weighted one; and, for the Gaussian series, nonnegativity, evenness and convexity of both statistics with the two expectation bounds.

**Formalization Note** `M` is any symmetric matrix with `‖M‖ ≤ L√n`, which includes the skipped phase `M = 0`; the proof uses nothing else about the partial sum. The Gaussian series runs over all of `ι`, with `m = |ι| ≤ wn`. `Integrable` is part of the conclusion, so the Bochner integrals mean what they say. -/
theorem lemma_8_48 {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι]
    (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.PosSemidef) (hT1 : (1 - T).PosSemidef)
    (A : ι → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, IsSymmContraction (A i)) (τ : ℕ → ℝ)
    (hτ : ∀ j : ℕ, 1 ≤ j → (T ^ (2 * j)).trace ≤ n * τ j)
    (M : Matrix (Fin n) (Fin n) ℝ) (hMs : M.IsSymm) {L C : ℝ} (hL : 0 < L) (hLC : L < C)
    (hM : ‖M‖ ≤ L * Real.sqrt n) :
    let B : ι → Matrix (Fin n) (Fin n) ℝ := fun i => sqrtM T * A i * sqrtM T
    let H : Matrix (Fin n) (Fin n) ℝ := (C * Real.sqrt n) • 1 - absM M
    let K : Matrix (Fin n) (Fin n) ℝ := ((C - L) * Real.sqrt n) • H⁻¹
    let T' : Matrix (Fin n) (Fin n) ℝ := sqrtM K * T * sqrtM K
    let U : Matrix (Fin n) (Fin n) ℝ := (L * Real.sqrt n)⁻¹ • absM M
    ((∃ A' : ι → Matrix (Fin n) (Fin n) ℝ, (∀ i, IsSymmContraction (A' i)) ∧
        ∀ i, sqrtM K * B i * sqrtM K = sqrtM T' * A' i * sqrtM T') ∧
      T'.PosSemidef ∧ (1 - T').PosSemidef) ∧
    (∀ (k deg : ℕ) (a : ℕ → ℝ) (μ : ℝ), 1 ≤ k → (∀ j, 0 ≤ a j) →
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 → (C - L) ^ (2 * k) ≤
        (C - L * u) ^ (2 * k) * ∑ j ∈ Finset.range (deg + 1), a j * u ^ (2 * j)) →
      ((evenPoly a deg U - a 0 • (1 : Matrix (Fin n) (Fin n) ℝ)).trace ≤
          (1 + deltaMom) * n * μ →
        (T' ^ (2 * k)).trace ≤ n * (a 0 * τ k + (1 + deltaMom) * μ)) ∧
      (1 ≤ deg → weightedStat T k deg a U ≤ (1 + deltaMom) * n * μ →
        (T' ^ (2 * k)).trace ≤ n * (a 0 * τ k + (1 + deltaMom) * μ))) ∧
    (∀ (k deg : ℕ) (a : ℕ → ℝ) (w η : ℝ), 1 ≤ k → (∀ j, 0 ≤ a j) →
      (Fintype.card ι : ℝ) ≤ w * n → w ≤ L ^ 2 * sPlus ^ 2 * η →
      let X : (ι → ℝ) → Matrix (Fin n) (Fin n) ℝ := fun ξ =>
        (sPlus * L * Real.sqrt n)⁻¹ • signedSum B ξ
      let f₁ : (ι → ℝ) → ℝ := fun ξ =>
        (evenPoly a deg (X ξ) - a 0 • (1 : Matrix (Fin n) (Fin n) ℝ)).trace
      let f₂ : (ι → ℝ) → ℝ := fun ξ => weightedStat T k deg a (X ξ)
      ((∀ ξ, 0 ≤ f₁ ξ) ∧ (∀ ξ, f₁ (-ξ) = f₁ ξ) ∧ ConvexOn ℝ Set.univ f₁ ∧
        Integrable f₁ (gammaM ι) ∧
        ∫ ξ, f₁ ξ ∂(gammaM ι) ≤
          n * ∑ j ∈ Finset.Icc 1 deg, a j * df j * η ^ j * τ j) ∧
      (1 ≤ deg →
        (∀ ξ, 0 ≤ f₂ ξ) ∧ (∀ ξ, f₂ (-ξ) = f₂ ξ) ∧ ConvexOn ℝ Set.univ f₂ ∧
        Integrable f₂ (gammaM ι) ∧
        ∫ ξ, f₂ ξ ∂(gammaM ι) ≤
          n * (a 1 * η * τ (k + 1) +
            ∑ j ∈ Finset.Icc 2 deg, a j * df j * η ^ j * τ j))) := by sorry

end SpencerEight
