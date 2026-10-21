-- Prove2me | Theorems.Thm_PowerFIPP_Charact_lemma_3_2_ii
-- name    : PowerFIPP.Charact.lemma_3_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:38.208998+00:00
-- url     : https://prove2.me/theorems/b34a72fe-10fc-43f8-91a6-d46235780c57
-- title:
--   Lemma 3.2 (ii), p. 9 — U is a P-FIPP with π* iff U^V is a Q^M-FIPP with π*
-- statement:
--   Under the assumptions of Lemma 3.2 (i) (standing assumptions, $p\in(-\infty,0)\cup(0,1)$, (A_D), $M$ and $V$ of Lemma 3.1, and $Q^M\in\mathcal Q_M$ with $dQ^M/dP|_{\mathcal F_t}=\mathcal E_t(M)$), for every predictable $\pi^*$:
--   $$U\ \text{is a } P\text{-FIPP with optimal } \pi^*\in\Gamma^P_{\mathcal C}\iff U^V\ \text{is a } Q^M\text{-FIPP with optimal } \pi^*\in\Gamma^{Q^M}_{\mathcal C},$$
--   where $U_t(x)=e^{D_t}x^p/p$ (equal to (3.4) by Lemma 3.1) and $U^V_t(x)=U_0(x)\mathcal E_t(V)$ (3.5), and FIPP is Definition 2.2.
--
--   The lemma removes the factor $\mathcal E(M)$ from the random field by an equivalent change of measure; the proof of Theorem 3.3 works entirely under $Q^M$.
--
--   **Formalization Note** Wealth processes are $x\mathcal E(\pi\cdot R)$ with $\pi\cdot R$ computed from the $P$-characteristics of $R$ (the same process under $Q^M$).
-- source:
--   Bo, Capponi & Zhou, Power forward performance in semimartingale markets with stochastic integrated factors, arXiv:1811.11899v4, p. 9, Lemma 3.2 (ii)

import Mathlib
import Definitions.Def_PowerFIPP_Charact_Model

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

namespace PowerFIPP.Charact

/-- **Lemma 3.2 (ii)** (p. 9). If `Q^M` of (3.6) belongs to `𝒬_M`, then `U` (3.1)/(3.4) is a
`P`-FIPP with optimal trading strategy `π* ∈ Γ^P_𝒞` iff `U^V` (3.5) is a `Q^M`-FIPP with optimal
trading strategy `π* ∈ Γ^{Q^M}_𝒞`. -/
theorem lemma_3_2_ii {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (mkt : Market Ω n) (p : ℝ)
    (hS : mkt.Standing P ℱ) (hp0 : p ≠ 0) (hp1 : p < 1) (hAD : AD P mkt)
    (M Dc J : ℝ≥0 → Ω → ℝ) (hM : IsLemma31MV P ℱ mkt M Dc J)
    (Q : Measure Ω) (hQ : IsQM P ℱ mkt M Q) (πstar : ℝ≥0 → Ω → Fin n → ℝ) :
    IsFIPP P P ℱ mkt (U mkt p) πstar ↔ IsFIPP Q P ℱ mkt (UV mkt p) πstar := by sorry

end PowerFIPP.Charact
