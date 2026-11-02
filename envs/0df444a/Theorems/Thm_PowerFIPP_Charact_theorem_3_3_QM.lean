-- Prove2me | Theorems.Thm_PowerFIPP_Charact_theorem_3_3_QM
-- name    : PowerFIPP.Charact.theorem_3_3_QM
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-01T10:21:54.523418+00:00
-- url     : https://prove2.me/theorems/8f5fada2-1664-4767-a0b6-edd07040de6d
-- title:
--   Theorem 3.3 under Q^M (proof, pp. 10–11) — U^V is a Q^M-FIPP with π* iff conditions (i)–(iii)
-- statement:
--   This is the form in which Bo, Capponi and Zhou actually prove Theorem 3.3: after the change of measure of Lemma 3.2, the characterization is carried out for the random field $U^V$ under $Q^M$.
--
--   Let an investor trade $n$ risky assets with cumulative returns $R$, a càdlàg $P$-semimartingale with differential characteristics $(b,c,F)$, under portfolio constraints $\mathcal C_t(\omega)$ satisfying (A_C), and let $D$ be a scalar $P$-semimartingale with characteristics $(b^D,c^D,F^D)$ satisfying (A_D). Fix $p\in(-\infty,0)\cup(0,1)$. Let
--   $$M=D^c+(e^v-1)*(\mu^D-\nu^D),\qquad V=B^D+\tfrac{C^D}{2}+\{e^v-1-h^D(v)\}*\nu^D$$
--   as in (3.3), let $Q^M\in\mathcal Q_M$ with $dQ^M/dP|_{\mathcal F_t}=\mathcal E_t(M)$, and consider the random field
--   $$U^V_t(x)=U_0(x)\,\mathcal E_t(V),\qquad U_0(x)=\frac{e^{D_0}}{p}x^p,\quad x>0 .$$
--   Let $(b^M,c,F^M)$ be the differential characteristics of $R$ under $Q^M$, $R^{M,c}$ its continuous martingale part under $Q^M$, and let $\pi^*\in\Gamma^{Q^M}_{\mathcal C}$ (admissibility for $U^V$ under $Q^M$, Definition 2.1). Then $U^V$ is a $Q^M$-FIPP with optimal trading strategy $\pi^*$ (Definition 2.2) if and only if, $P(d\omega)\otimes dt$-a.s.:
--   1. $\mathcal E\big(\beta^M\cdot R^{M,c}+\overline W^M(u)*(\mu-\nu^M)\big)\,\mathcal E(M)$ is a $P$-martingale, where $\beta^M=p\pi^*$ and $\overline W^M_t(u)=\{1+(\pi^*_t)^\top u\}^p-1$;
--   2. $\Phi^M_p(\pi^*)=\sup_{\pi\in\mathcal C\cap\mathcal C_0}\Phi^M_p(\pi)$;
--   3. the characteristics of $D$ satisfy (3.7):
--   $$\sup_{\pi\in\mathcal C\cap\mathcal C_0}\Phi^M_p(\pi)+p^{-1}\Big\{b^D+\frac{c^D}{2}+(e^v-1-h^D(v))*F^D\Big\}=0,$$
--   with $\Phi^M_p(\pi)=\pi^\top b^M+\frac{p-1}{2}\pi^\top c\pi+\{p^{-1}(1+\pi^\top u)^p-p^{-1}-\pi^\top h(u)\}*F^M$ as in (3.8).
--
--   Combined with Lemma 3.2 (i) ($\Gamma^P_{\mathcal C}=\Gamma^{Q^M}_{\mathcal C}$) and Lemma 3.2 (ii) ($U$ is a $P$-FIPP with $\pi^*$ iff $U^V$ is a $Q^M$-FIPP with $\pi^*$), this statement yields Theorem 3.3; the paper's proof of Theorem 3.3 opens with exactly this reduction ("By Lemma 3.2, it is enough to prove that $U^V$ given by (3.5) is a $Q^M$-FIPP with the optimal trading strategy $\pi^*\in\Gamma^{Q^M}_{\mathcal C}$ if and only if (i)–(iii) hold").
--
--   **Formalization Note** All objects and hypotheses are those of `PowerFIPP.Charact.theorem_3_3` (definitions file `PowerFIPP_Charact_Model`), with the only changes that the field is `UV mkt p` under `Q`, and the admissibility hypothesis is $\pi^*\in\Gamma^{Q}_{\mathcal C}$ for `UV` (`Gamma Q P ℱ mkt (UV mkt p)`). Conditions (i)–(iii) are the same predicates `cond_i`, `cond_ii`, `cond_iii` as in Theorem 3.3.
-- source:
--   Bo, Capponi & Zhou, Power forward performance in semimartingale markets with stochastic integrated factors, arXiv:1811.11899v4, proof of Theorem 3.3, pp. 10–11 (first sentence: 'By Lemma 3.2, it is enough to prove that U^V given by (3.5) is a Q^M-FIPP with the optimal trading strategy π* ∈ Γ^{Q^M}_C if and only if (i)-(iii) hold'), with (3.5), (3.7)–(3.8)

import Mathlib
import Definitions.Def_PowerFIPP_Charact_Model

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

namespace PowerFIPP.Charact

/-- **Theorem 3.3 under `Q^M`** (proof of Theorem 3.3, pp. 10–11). Under the conditions of
Theorem 3.3, the random field `U^V` (3.5) is a `Q^M`-FIPP with optimal trading strategy
`π* ∈ Γ^{Q^M}_𝒞` iff conditions (i)–(iii) of Theorem 3.3 hold. -/
theorem theorem_3_3_QM {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (mkt : Market Ω n) (p : ℝ)
    (hS : mkt.Standing P ℱ) (hp0 : p ≠ 0) (hp1 : p < 1) (hAC : AC mkt) (hAD : AD P mkt)
    (M Dc J : ℝ≥0 → Ω → ℝ) (hM : IsLemma31MV P ℱ mkt M Dc J)
    (Q : Measure Ω) (hQ : IsQM P ℱ mkt M Q)
    (bM : ℝ≥0 → Ω → Fin n → ℝ) (FM : ℝ≥0 → Ω → Measure (Fin n → ℝ))
    (hchar : IsDiffChar Q ℱ mkt.R bM mkt.c FM)
    (RMc : ℝ≥0 → Ω → Fin n → ℝ) (hRMc : IsContPart Q ℱ mkt.R bM RMc)
    (πstar : ℝ≥0 → Ω → Fin n → ℝ) (hπ : πstar ∈ Gamma Q P ℱ mkt (UV mkt p)) :
    IsFIPP Q P ℱ mkt (UV mkt p) πstar ↔
      cond_i P Q ℱ mkt p M RMc πstar ∧ cond_ii P mkt p bM FM πstar ∧
        cond_iii P mkt p bM FM := by sorry

end PowerFIPP.Charact
