-- Prove2me | Theorems.Thm_PowerFIPP_Charact_theorem_3_3
-- name    : PowerFIPP.Charact.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:46.179988+00:00
-- url     : https://prove2.me/theorems/338728b9-efeb-4c96-956a-ec13c6e24007
-- title:
--   Theorem 3.3, p. 9 — U = e^D x^p/p is a P-FIPP with optimal π* iff (i) the martingale condition, (ii) π* maximizes Φ^M_p on 𝒞 ∩ 𝒞_0, (iii) the drift equation (3.7)
-- statement:
--   Let an investor trade $n$ risky assets with cumulative returns $R$, a càdlàg semimartingale with differential characteristics $(b,c,F)$, under portfolio constraints $\mathcal C_t(\omega)$, and let $D$ be a scalar semimartingale with characteristics $(b^D,c^D,F^D)$. Fix $p\in(-\infty,0)\cup(0,1)$ and consider the power random field
--   $$U_t(x)=\frac{e^{D_t}}{p}x^p,\qquad x>0.$$
--   Assume (A_C), (A_D) and the conditions of Lemmas 3.1–3.2: $M=D^c+(e^v-1)*(\mu^D-\nu^D)$, and $Q^M\in\mathcal Q_M$ with $dQ^M/dP|_{\mathcal F_t}=\mathcal E_t(M)$. Let $(b^M,c,F^M)$ be the characteristics of $R$ under $Q^M$, $\nu^M(dt,du)=F^M_t(du)dt$, $R^{M,c}$ the continuous martingale part of $R$ under $Q^M$, and let $\pi^*\in\Gamma^P_{\mathcal C}$. Then $U$ is a $P$-FIPP with optimal trading strategy $\pi^*$ if and only if:
--   1. $\mathcal E\big(\beta^M\cdot R^{M,c}+\overline W^M(u)*(\mu-\nu^M)\big)\mathcal E(M)$ is a $P$-martingale, where $\beta^M=p\pi^*$ and $\overline W^M_t(u)=\{1+(\pi^*_t)^\top u\}^p-1$;
--   2. $\Phi^M_p(\pi^*)=\sup_{\pi\in\mathcal C\cap\mathcal C_0}\Phi^M_p(\pi)$, $P(d\omega)\otimes dt$-a.s.;
--   3. $P(d\omega)\otimes dt$-a.s.,
--   $$\sup_{\pi\in\mathcal C\cap\mathcal C_0}\Phi^M_p(\pi)+p^{-1}\Big\{b^D+\frac{c^D}{2}+(e^v-1-h^D(v))*F^D\Big\}=0,\tag{3.7}$$
--   with $\Phi^M_p(\pi)=\pi^\top b^M+\frac{p-1}{2}\pi^\top c\pi+\{p^{-1}(1+\pi^\top u)^p-p^{-1}-\pi^\top h(u)\}*F^M$ (3.8).
--
--   The theorem characterizes, through the drift and jump characteristics of $D$, all power forward performance processes of the form $e^{D}x^p/p$, together with their optimal strategies, in a general semimartingale market with constraints.
--
--   **Formalization Note** $\pi^*$ is fixed on both sides: the page's "there exists $\pi^*\in\Gamma^P_{\mathcal C}$" in (ii) refers to the strategy named in the statement, which condition (i) also uses. "The random field $U$ given by (3.4)" is taken in the form (3.1), equal to (3.4) by Lemma 3.1. $(b^M,F^M)$ and $R^{M,c}$ are hypotheses characterizing them as the characteristics and continuous martingale part of $R$ under $Q^M$ rather than through the Girsanov formulas (2.7)–(2.8); they agree $Q^M\otimes dt$-a.e. (Jacod–Shiryaev III.3.24). $R$-integrability is the canonical-decomposition class of the calculus layer, under $P$. At zero wealth the field is $0$ ($p>0$) or $-\infty$ ($p<0$). The integrals in (i) are required to exist, and (iii) includes the finiteness of the $F^D$-integral.
-- source:
--   Bo, Capponi & Zhou, Power forward performance in semimartingale markets with stochastic integrated factors, arXiv:1811.11899v4, p. 9, Theorem 3.3 (with (3.7)–(3.8))

import Mathlib
import Definitions.Def_PowerFIPP_Charact_Model

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

namespace PowerFIPP.Charact

/-- **Theorem 3.3** (p. 9). Let (A_C) and the conditions of Lemmas 3.1–3.2 hold. The random field
`U` (3.1) (equal to (3.4) by Lemma 3.1) is a `P`-FIPP with optimal trading strategy
`π* ∈ Γ^P_𝒞` iff, `P(dω) ⊗ dt`-a.s.:
(i) `𝓔(β^M · R^{M,c} + W̄^M(u) ∗ (μ - ν^M)) 𝓔(M)` is a `P`-martingale;
(ii) `Φ^M_p(π*) = sup_{π ∈ 𝒞 ∩ 𝒞_0} Φ^M_p(π)`;
(iii) the characteristics of `D` satisfy (3.7). -/
theorem theorem_3_3 {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (mkt : Market Ω n) (p : ℝ)
    (hS : mkt.Standing P ℱ) (hp0 : p ≠ 0) (hp1 : p < 1) (hAC : AC mkt) (hAD : AD P mkt)
    (M Dc J : ℝ≥0 → Ω → ℝ) (hM : IsLemma31MV P ℱ mkt M Dc J)
    (Q : Measure Ω) (hQ : IsQM P ℱ mkt M Q)
    (bM : ℝ≥0 → Ω → Fin n → ℝ) (FM : ℝ≥0 → Ω → Measure (Fin n → ℝ))
    (hchar : IsDiffChar Q ℱ mkt.R bM mkt.c FM)
    (RMc : ℝ≥0 → Ω → Fin n → ℝ) (hRMc : IsContPart Q ℱ mkt.R bM RMc)
    (πstar : ℝ≥0 → Ω → Fin n → ℝ) (hπ : πstar ∈ Gamma P P ℱ mkt (U mkt p)) :
    IsFIPP P P ℱ mkt (U mkt p) πstar ↔
      cond_i P Q ℱ mkt p M RMc πstar ∧ cond_ii P mkt p bM FM πstar ∧
        cond_iii P mkt p bM FM := by sorry

end PowerFIPP.Charact
