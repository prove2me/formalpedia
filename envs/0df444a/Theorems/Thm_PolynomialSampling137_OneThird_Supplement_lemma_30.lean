-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_Supplement_lemma_30
-- name    : PolynomialSampling137.OneThird.Supplement.lemma_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:56:18.615949+00:00
-- url     : https://prove2.me/theorems/ca334376-4021-47a4-9597-011380e5508a
-- title:
--   Lemma 30 — Uniform circuit acceptance gaps for every non-dyadic real p and exact one-third gap
-- statement:
--   For every fixed $q\ge0$ and every non-dyadic real $p\in(0,1)$, there is $\delta_{q,p}>0$, chosen before the seed length and function, such that every $f\in\mathcal C_q$ satisfies
--   $$|\Pr[f(U_s)=1]-p|\ge\delta_{q,p}.$$
--   Uniformly for all $q,s$ and $f\in\mathcal C_q$, at $p=1/3$ one may take $\delta_q=1/(3\,4^{2^q})$. Irrational non-dyadic parameters are included. These acceptance gaps concern the actual finite circuit class with unbounded fan-in, XOR/NOT count and depth.
--
--   Differences from the source:
--   - encoding: finite binary vector spaces and probability laws → Fin-indexed words, finite fiber sums and structural predicates; reason: the representations preserve all source instances, including zero dimensions and zero masses
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Lemma 30, printed p. 38; PDF p. 40

import Definitions.Def_PolynomialSampling137_OneThird_Supplement_Circuits

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

theorem lemma_30 :
    (∀ (q : ℕ) (p : ℝ), 0 < p → p < 1 → NonDyadic p →
      ∃ δ : ℝ, 0 < δ ∧ ∀ (s : ℕ) (f : Word s → ZMod 2),
        InCircuitClass q f → δ ≤ |acceptance f - p|) ∧
    (∀ (q s : ℕ) (f : Word s → ZMod 2), InCircuitClass q f →
      1 / (3 * (4 : ℝ) ^ (2 ^ q)) ≤ |acceptance f - 1/3|) := by sorry

end PolynomialSampling137.OneThird.Supplement
