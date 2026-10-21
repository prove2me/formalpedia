-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_lemma18_filter
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.lemma18_filter
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:01:25.787978+00:00
-- url     : https://prove2.me/theorems/d269687a-cd9d-44c5-9354-f33e131c44d4
-- title:
--   Lemma 18 (Filtering lemma)
-- statement:
--   Let $S$ be any finite set of phase-free $n$-qubit Paulis, possibly empty. Let $\widetilde\epsilon,\eta,A>0$ and $1\le r<2$. For every $P\in S$, suppose $|\alpha_P|\le\eta$, $\beta_P\in[0,1]$, $x_P=\alpha_P\beta_P$, and $\sum_{P\in S}|\alpha_P|^r\le A^r$. Assume the strict uniform errors $|\widehat x_P-x_P|<\eta\widetilde\epsilon$ and $|\widehat\beta_P-\beta_P|<\widetilde\epsilon$. Set $\widehat\alpha_P=0$ if $\widehat\beta_P\le2\widetilde\epsilon$, or if $\widehat\beta_P>2\widetilde\epsilon$ and $|\widehat x_P|/\sqrt{\widehat\beta_P}\le2\eta\sqrt{\widetilde\epsilon}$; otherwise set $\widehat\alpha_P=\widehat x_P/\widehat\beta_P$. Both conclusions hold:
--   $$\sum_{P\in S}\beta_P|\widehat\alpha_P-\alpha_P|^2\le6A^r\eta^{2-r}\widetilde\epsilon^{1-r/2},\qquad\beta_P|\widehat\alpha_P-\alpha_P|^2\le9\eta^2\widetilde\epsilon\quad(P\in S).$$
--   This provides simultaneous aggregate and per-coefficient control after both filtering layers.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 38, Lemma 18 (Filtering lemma)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Lemma 18, paper pp.38-39, D27-D28: retain BOTH the summed bound and
every individual bound. The finite set may be empty. -/
theorem lemma18_filter (n : ℕ) (S : Finset ((Fin n → Fin 4))) (e eta A r : ℝ)
    (he : 0 < e) (heta : 0 < eta) (hA : 0 < A) (hr1 : 1 ≤ r) (hr2 : r < 2)
    (alpha beta xhat bhat : (Fin n → Fin 4) → ℝ)
    (ha : ∀ P ∈ S, |alpha P| ≤ eta)
    (hb : ∀ P ∈ S, 0 ≤ beta P ∧ beta P ≤ 1)
    (hmass : ∑ P ∈ S, Real.rpow |alpha P| r ≤ Real.rpow A r)
    (hx : ∀ P ∈ S, |xhat P - alpha P * beta P| < eta * e)
    (hbe : ∀ P ∈ S, |bhat P - beta P| < e) :
    (∑ P ∈ S, beta P * |sparseFilter e eta (xhat P) (bhat P) - alpha P| ^ 2) ≤
      6 * Real.rpow A r * Real.rpow eta (2 - r) * Real.rpow e (1 - r / 2) ∧
    ∀ P ∈ S, beta P * |sparseFilter e eta (xhat P) (bhat P) - alpha P| ^ 2 ≤
      9 * eta ^ 2 * e := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
