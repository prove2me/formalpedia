-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_iid_finite_extractor
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.iid_finite_extractor
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:49:36.043666+00:00
-- url     : https://prove2.me/theorems/f6cd69a3-d84a-426a-b40f-40fa4cba0e24
-- title:
--   Lemma 4 (48)
-- statement:
--   All logarithms are natural and $d_1$ is the full $L^1$ distance. Let $P$ be a normalized law on a finite nonempty alphabet $A$, and let $U_M$ be the uniform law on $M\ge1$ symbols. For a map $f$, write $f_*P$ for its pushforward. Fix $n\ge1$ and $M\ge1$. Let $T_n$ be the realized empirical types, $T_n(Q)$ their word classes, $v_Q=\prod_aP(a)^{nQ(a)}$ their common atom probability, and $m_Q=P^n(T_n(Q))$. Set $T_n^1[M]=\{Q:v_Q\le1/M\}$ and $T_n^2[M]=\{Q:m_Q<1/M\}$. There exists $f:A^n\to\{1,\ldots,M\}$ with
--   $$d_1(f_*P^n,U_M)\le2P^n\{P^n(x)\ge1/M\}+2\sum_{Q\in T_n^1[M]}Mv_Qm_Q+2|T_n|\max_{Q\in T_n^2[M]}v_Q.$$
--   An impossible type has $v_Q=0$ and an empty maximum is zero. The two displayed type sets may overlap. This retains every term of (48).
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 8, Lemma 4 (48)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF pp.8–9, Lemma 4, (48): all three terms and overlapping type sets. -/
theorem iid_finite_extractor {A : Type*} [Fintype A] [Nonempty A]
    (P : A → ℝ) (hP : IsLaw P) (n M : ℕ) (hn : 0 < n) (hM : 0 < M) :
    ∃ f : (Fin n → A) → Fin M,
      extractionError (iid P n) f ≤
        2 * (∑ x : Fin n → A, if 1 / (M : ℝ) ≤ iid P n x then iid P n x else 0) +
        2 * (∑ q ∈ firstTypes P n M, (M : ℝ) * typeAtom P q * typeMass P n q) +
        2 * ((types A n).card : ℝ) * rareTypePeak P n M := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
