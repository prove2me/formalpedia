-- Prove2me | Theorems.Thm_PowerFIPP_Charact_lemma_3_4
-- name    : PowerFIPP.Charact.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:43.609282+00:00
-- url     : https://prove2.me/theorems/4c1b6aa7-c691-4b38-840e-a40610e189b5
-- title:
--   Lemma 3.4, p. 10 — if U^V is a Q^M-FIPP, every admissible π has the integrability of (3.10), and D's characteristics satisfy (3.7) Q^M⊗dt-a.s.
-- statement:
--   Assume the conditions of Theorem 3.3: the standing assumptions, $p\in(-\infty,0)\cup(0,1)$, (A_C), (A_D), $M$ and $V$ of Lemma 3.1, and $Q^M\in\mathcal Q_M$. Let $(b^M,c,F^M)$ be the differential characteristics of $R$ under $Q^M$, $\nu^M(dt,du)=F^M_t(du)dt$, and $R^{M,c}$ the continuous martingale part of $R$ under $Q^M$. Suppose $U^V_t(x)=U_0(x)\mathcal E_t(V)$ is a $Q^M$-FIPP with some optimal strategy $\pi^*$. Then for every $\pi\in\Gamma^{Q^M}_{\mathcal C}$:
--   1. $\pi\in L^{Q^M,2}_{loc}(R^{M,c})$, i.e. $\pi\cdot R^{M,c}$ exists;
--   2. $W^\pi\in G^{Q^M}_{loc}(\mu)$, i.e. $W^\pi*(\mu-\nu^M)$ exists, where $W^\pi_t(u)=p^{-1}(1+\pi_t^\top u)^p-p^{-1}$ (3.9);
--   3. $\big|p^{-1}(1+\pi^\top u)^p-p^{-1}-\pi^\top h(u)\big|*\nu^M\in\mathcal A^{Q^M,+}_{loc}$: there are stopping times $\tau_k\uparrow\infty$ with $E^{Q^M}\big[\int_0^{\tau_k}\!\int|\cdots|F^M_s(du)\,ds\big]<\infty$.
--
--   Moreover the characteristics $(b^D,c^D,F^D)$ of $D$ satisfy (3.7),
--   $$\sup_{\pi\in\mathcal C\cap\mathcal C_0}\Phi^M_p(\pi)+p^{-1}\Big\{b^D+\frac{c^D}{2}+(e^v-1-h^D(v))*F^D\Big\}=0,\qquad Q^M(d\omega)\otimes dt\text{-a.s.}$$
--
--   This lemma provides the necessity half of Theorem 3.3: the FIPP property forces equation (3.7) and the integrability needed to write $U^V(X^{\pi,x})$ as the stochastic exponential (3.10).
--
--   **Formalization Note** "The conditions of Theorem 3.3" are read as the theorem's hypotheses, not its conditions (i)–(iii). At $1+\pi^\top u=0$ with $p<0$ the integrand is $+\infty$ in absolute value; for admissible $\pi$ this set is $F^M$-null a.e. (3.7) includes the finiteness of the $F^D$-integral.
-- source:
--   Bo, Capponi & Zhou, Power forward performance in semimartingale markets with stochastic integrated factors, arXiv:1811.11899v4, p. 10, Lemma 3.4

import Mathlib
import Definitions.Def_PowerFIPP_Charact_Model

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

namespace PowerFIPP.Charact

/-- **Lemma 3.4** (p. 10). Under the conditions of Theorem 3.3, if `U^V` (3.5) is a `Q^M`-FIPP,
then for every `π ∈ Γ^{Q^M}_𝒞`: `π ∈ L^{Q^M,2}_loc(R^{M,c})`, `W^π ∈ G^{Q^M}_loc(μ)`, and
`|p^{-1}(1 + π^⊤u)^p - p^{-1} - π^⊤h(u)| ∗ ν^M ∈ 𝒜^{Q^M,+}_loc`; moreover the characteristics of
`D` satisfy (3.7), `Q^M(dω) ⊗ dt`-a.s. -/
theorem lemma_3_4 {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (mkt : Market Ω n) (p : ℝ)
    (hS : mkt.Standing P ℱ) (hp0 : p ≠ 0) (hp1 : p < 1) (hAC : AC mkt) (hAD : AD P mkt)
    (M Dc J : ℝ≥0 → Ω → ℝ) (hM : IsLemma31MV P ℱ mkt M Dc J)
    (Q : Measure Ω) (hQ : IsQM P ℱ mkt M Q)
    (bM : ℝ≥0 → Ω → Fin n → ℝ) (FM : ℝ≥0 → Ω → Measure (Fin n → ℝ))
    (hchar : IsDiffChar Q ℱ mkt.R bM mkt.c FM)
    (RMc : ℝ≥0 → Ω → Fin n → ℝ) (hRMc : IsContPart Q ℱ mkt.R bM RMc)
    (πstar : ℝ≥0 → Ω → Fin n → ℝ) (hF : IsFIPP Q P ℱ mkt (UV mkt p) πstar) :
    (∀ π ∈ Gamma Q P ℱ mkt (UV mkt p),
      (∃ L : ℝ≥0 → Ω → ℝ, IsContIntegral Q ℱ RMc mkt.c π L) ∧
      (∃ N : ℝ≥0 → Ω → ℝ, IsCompJumpIntegral Q ℱ mkt.R (Wpi p π) N) ∧
      (∃ τ : ℕ → Ω → WithTop ℝ≥0, IsLocalizingSequence ℱ τ Q ∧
        ∀ k, ∫⁻ ω, ∫⁻ s in {s : ℝ≥0 | (s : WithTop ℝ≥0) ≤ τ k ω},
          ∫⁻ u, ((phiIntegrand p (π s ω) u).toENNReal +
            (-phiIntegrand p (π s ω) u).toENNReal) ∂FM s ω ∂leb ∂Q < ∞)) ∧
    cond_iii Q mkt p bM FM := by sorry

end PowerFIPP.Charact
