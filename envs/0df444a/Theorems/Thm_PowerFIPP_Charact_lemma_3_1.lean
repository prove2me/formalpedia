-- Prove2me | Theorems.Thm_PowerFIPP_Charact_lemma_3_1
-- name    : PowerFIPP.Charact.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:36.985228+00:00
-- url     : https://prove2.me/theorems/cbfdb165-ca61-498c-a978-f548ff2fa184
-- title:
--   Lemma 3.1, p. 8 — e^D = e^{D_0}𝓔(M)𝓔(V) with M = D^c + (e^v−1)∗(µ^D−ν^D) a local martingale and V continuous of finite variation
-- statement:
--   Assume the standing assumptions of §2 and Assumption (A_D)-(i) or (ii) on the scalar semimartingale $D$, whose characteristics under $P$ are $(b^D,c^D,F^D)$. Let $D^c$ be the continuous martingale part of $D$, $\mu^D$ its jump measure with compensator $\nu^D(dt,dv)=F^D_t(dv)dt$, and
--   $$M=D^c+(e^v-1)*(\mu^D-\nu^D),\qquad V=\int_0^\cdot\Big(b^D_s+\frac{c^D_s}2+\int\big(e^v-1-h^D(v)\big)F^D_s(dv)\Big)ds.$$
--   Then $M$ exists, and for it the following hold:
--   1. $P$-a.s., for all $t\ge0$, $e^{D_t}=e^{D_0}\,\mathcal E_t(M)\,\mathcal E_t(V)$ (3.2);
--   2. $M$ is a $P$-local martingale;
--   3. $V$ is adapted, and $P$-a.s. continuous with locally bounded variation;
--   4. $P$-a.s., $\Delta M_t=(e^{\Delta D_t}-1)\mathbf 1_{\{\Delta D_t\ne0\}}$ for all $t$.
--
--   This multiplicative decomposition turns the power field $U_t(x)=e^{D_t}x^p/p$ into $U_0(x)\mathcal E_t(M)\mathcal E_t(V)$ (3.4), the starting point of the change of measure in Lemma 3.2.
--
--   **Formalization Note** $\langle M^c\rangle=\int c^D\,ds$ is the quadratic-variation input of $\mathcal E(M)$, and $\mathcal E(V)$ uses $\langle V^c\rangle=0$. "$V\in\mathcal V^P\cap\mathcal P$" is stated as adapted, continuous and of locally bounded variation (a continuous adapted process is predictable).
-- source:
--   Bo, Capponi & Zhou, Power forward performance in semimartingale markets with stochastic integrated factors, arXiv:1811.11899v4, p. 8, Lemma 3.1, (3.2)–(3.3)

import Mathlib
import Definitions.Def_PowerFIPP_Charact_Model

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

namespace PowerFIPP.Charact

/-- **Lemma 3.1** (p. 8). Under (A_D), the process `M = D^c + (e^v - 1) ∗ (μ^D - ν^D)` of (3.3)
exists, and for any such `M` (with `V` of (3.3)): `P`-a.s. `e^{D} = e^{D_0} 𝓔(M) 𝓔(V)` (3.2);
`M` is a `P`-local martingale; `V` is adapted, continuous and of finite variation; and
`ΔM = (e^{ΔD} - 1) 1_{ΔD ≠ 0}`. -/
theorem lemma_3_1 {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (mkt : Market Ω n)
    (hS : mkt.Standing P ℱ) (hAD : AD P mkt) :
    (∃ M Dc J : ℝ≥0 → Ω → ℝ, IsLemma31MV P ℱ mkt M Dc J) ∧
    ∀ M Dc J : ℝ≥0 → Ω → ℝ, IsLemma31MV P ℱ mkt M Dc J →
      (∀ᵐ ω ∂P, ∀ t, Real.exp (mkt.D t ω) =
        Real.exp (mkt.D 0 ω) * EM mkt M t ω * stochExp (V mkt) (fun _ _ => 0) t ω) ∧
      IsLocMart P ℱ M ∧
      StronglyAdapted ℱ (V mkt) ∧
      (∀ᵐ ω ∂P, Continuous (fun t => V mkt t ω) ∧
        LocallyBoundedVariationOn (fun t => V mkt t ω) Set.univ) ∧
      (∀ᵐ ω ∂P, ∀ t, jump M t ω =
        if jump mkt.D t ω ≠ 0 then Real.exp (jump mkt.D t ω) - 1 else 0) := by sorry

end PowerFIPP.Charact
