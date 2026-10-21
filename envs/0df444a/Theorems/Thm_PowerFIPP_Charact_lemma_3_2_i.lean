-- Prove2me | Theorems.Thm_PowerFIPP_Charact_lemma_3_2_i
-- name    : PowerFIPP.Charact.lemma_3_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:39.841498+00:00
-- url     : https://prove2.me/theorems/ced5dc70-328a-4590-958b-6e6eb20ad01c
-- title:
--   Lemma 3.2 (i), p. 9 — if Q^M ∈ 𝒬_M, then Γ^P_𝒞 = Γ^{Q^M}_𝒞
-- statement:
--   Assume the standing assumptions of §2, $p\in(-\infty,0)\cup(0,1)$ and (A_D), let $M$ be the local martingale of Lemma 3.1 and $V$ the process (3.3), and let $Q^M$ be defined by $dQ^M/dP|_{\mathcal F_t}=\mathcal E_t(M)$ (3.6). If $Q^M\in\mathcal Q_M$, then
--   $$\Gamma^P_{\mathcal C}=\Gamma^{Q^M}_{\mathcal C},$$
--   where $\Gamma^P_{\mathcal C}$ is the class of admissible strategies (Definition 2.1) associated with the power field $U_t(x)=e^{D_t}x^p/p$ under $P$ and $\Gamma^{Q^M}_{\mathcal C}$ the class associated with $U^V_t(x)=U_0(x)\mathcal E_t(V)$ under $Q^M$.
--
--   Together with Lemma 3.2 (ii), this reduces the characterization of $U$ as a $P$-FIPP to that of $U^V$ as a $Q^M$-FIPP.
--
--   **Formalization Note** In both classes the stochastic integral $\pi\cdot R$ is the one computed from the $P$-characteristics of $R$, which is the same process under $Q^M\sim P$; the classes differ only in the measure of the jump constraint and in the class (DL) clause.
-- source:
--   Bo, Capponi & Zhou, Power forward performance in semimartingale markets with stochastic integrated factors, arXiv:1811.11899v4, p. 9, Lemma 3.2 (i)

import Mathlib
import Definitions.Def_PowerFIPP_Charact_Model

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

namespace PowerFIPP.Charact

/-- **Lemma 3.2 (i)** (p. 9). If `Q^M` of (3.6) belongs to `𝒬_M`, then `Γ^P_𝒞 = Γ^{Q^M}_𝒞`: the
strategies admissible under `P` for `U` (3.1)/(3.4) are those admissible under `Q^M` for `U^V`
(3.5). -/
theorem lemma_3_2_i {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (mkt : Market Ω n) (p : ℝ)
    (hS : mkt.Standing P ℱ) (hp0 : p ≠ 0) (hp1 : p < 1) (hAD : AD P mkt)
    (M Dc J : ℝ≥0 → Ω → ℝ) (hM : IsLemma31MV P ℱ mkt M Dc J)
    (Q : Measure Ω) (hQ : IsQM P ℱ mkt M Q) :
    Gamma P P ℱ mkt (U mkt p) = Gamma Q P ℱ mkt (UV mkt p) := by sorry

end PowerFIPP.Charact
