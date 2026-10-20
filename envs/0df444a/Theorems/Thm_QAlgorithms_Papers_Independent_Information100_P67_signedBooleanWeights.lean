-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_signedBooleanWeights
-- name    : QAlgorithms.Papers.Independent.Information100.P67.signedBooleanWeights
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:53:29.514288+00:00
-- url     : https://prove2.me/theorems/b21289ae-9cb6-455c-adb7-fa3d302d5f37
-- title:
--   Lemma 4.1 (Signed Boolean weights)
-- statement:
--   There exist universal constants $C_{\rm app}\ge1$ and $a=1/(4C_{\rm app}^2)>0$ such that for every positive integer $n$ and nonnegative integer $t$ with $4C_{\rm app}\sqrt n\le t\le n/2$, there is a real symmetric matrix $W$ indexed by $\{0,1\}^n$. Write $U_0[x,y]=2^{-n}$, $V(n,t)=\sum_{j=0}^t\binom nj$, and $s(x,y)=|\{j:x_j=y_j\}|$. Then
--
--   $$W\mathbf1=\mathbf1,\quad \|W-U_0\|_{\rm op}\le2e^{-at^2/n},\quad \sum_y|W_{xy}|\le\sqrt{V(n,t)}\quad\text{for every }x,$$
--   $$W_{xy}\ne0\ \Longrightarrow\ s(x,y)\le t.$$
--
--   The allowed integer interval already forces $t\ge0$, so natural-number indexing changes no cases. The weights may have either sign. This is the signed-weight construction attributed to [KBK+26, Lemma S3].
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 19, Lemma 4.1 (Signed Boolean weights)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Information100.P67

variable {A B E R S T X C Y G1 G2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]

variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]

variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]

variable [Fintype G2] [DecidableEq G2]

/-- Lemma 4.1, PDF pp.19–21, attributed to [KBK+26, Lemma S3].
Universal constants precede n,t. Signed real weights need not be positive. -/
theorem signedBooleanWeights :
    ∃ Capp : ℝ, 1 ≤ Capp ∧ ∃ a : ℝ, 0 < a ∧ a = 1 / (4 * Capp ^ 2) ∧
    ∀ n : ℕ, 0 < n → ∀ t : ℕ,
      4 * Capp * Real.sqrt n ≤ (t : ℝ) → (t : ℝ) ≤ (n : ℝ) / 2 →
      ∃ W : Matrix (Fin n → Bool) (Fin n → Bool) ℝ,
        W.transpose = W ∧ (∀ x, ∑ y, W x y = 1) ∧
        specNorm (W - uniformLabelMatrix n) ≤ 2 * Real.exp (-a * (t : ℝ) ^ 2 / n) ∧
        (∀ x, ∑ y, |W x y| ≤ Real.sqrt (binomialVolume n t)) ∧
        (∀ x y, W x y ≠ 0 → agreementCount x y ≤ t) := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
