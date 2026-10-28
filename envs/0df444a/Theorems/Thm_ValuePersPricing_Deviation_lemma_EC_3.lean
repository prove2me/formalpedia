-- Prove2me | Theorems.Thm_ValuePersPricing_Deviation_lemma_EC_3
-- name    : ValuePersPricing.Deviation.lemma_EC_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:00.968394+00:00
-- url     : https://prove2.me/theorems/42916b69-e50e-4306-83ef-430cf3c165c4
-- title:
--   Lemma EC.3, p. ec7 — tight distributions F̄_L, F̄_M, F̄_H attaining (EC.5)–(EC.7) (corrected: (a) for D > 0; (c) last piece closed at S)
-- statement:
--   Let $S>1$, take cost $c=0$, and let $\delta_L,\delta_M,\delta_H$ be the thresholds at $M=1$. Each statement below asserts the existence of a probability law of a valuation $V\ge 0$ with mean $1$, scale $S$ and coefficient of deviation $D$ whose cCDF $\bar F(x)=\mathbb P(V\ge x)$ is, for $x\ge 0$, the stated function, and which attains the corresponding bound with equality.
--
--   1. **Low heterogeneity.** For $D\in(0,\delta_L]$, with $\alpha_L=\Big(\frac{W_{-1}((D-1)/e)}{D-1}\Big)^{-1}$,
--   $$\bar F_L(x)=\begin{cases}1 & 0\le x<\alpha_L\\ \alpha_L/x & \alpha_L\le x\le 1\\ \frac{D}{\log(S)\,x} & 1<x\le S\\ 0 & x>S,\end{cases}$$
--   and $\mathcal R_{PP}=\frac{W_{-1}((D-1)/e)}{D-1}\mathcal R_{SP}$ (Eq. (EC.5) with equality).
--   2. **Medium heterogeneity.** For $D\in[\delta_L,\delta_M]$, with $\alpha_M=D/\log S$,
--   $$\bar F_M(x)=\begin{cases}1 & x=0\\ \frac{\alpha_M}{e}S^{1/D-1} & 0<x<eS^{1-1/D}\\ \alpha_M/x & eS^{1-1/D}\le x\le S\\ 0 & x>S,\end{cases}$$
--   and $D\,\mathcal R_{PP}=\log(S)\,\mathcal R_{SP}$ (Eq. (EC.6) with equality).
--   3. **High heterogeneity.** For $D\in[\delta_M,\delta_H]$, with $\alpha_H=\big(-W_{-1}(-1/(eS(1-D)))\big)^{-1}$,
--   $$\bar F_H(x)=\begin{cases}1 & x=0\\ 1-D & 0<x\le\frac{\alpha_H}{1-D}\\ \alpha_H/x & \frac{\alpha_H}{1-D}<x\le S\\ 0 & x>S,\end{cases}$$
--   and $\mathcal R_{PP}=-W_{-1}\big(\frac{-1}{eS(1-D)}\big)\mathcal R_{SP}$ (Eq. (EC.7) with equality).
--
--   These laws show that the bounds of Theorem 2 are tight in the standardized case; Lemma 1 transports them to a general cost and mean.
--
--   Differences from the source:
--   - correction: (a) "Suppose D ∈ [0, δL]" → D ∈ (0, δL]; reason: at D = 0, α_L = 1 and F̄_L is the point mass at 1, whose scale is 1, not S > 1 (e.g. S = 2).
--   - correction: (c) third piece "α_H/x if x ∈ (α_H/(1−D), S)", "0 otherwise" → α_H/x on (α_H/(1−D), S]; reason: as printed F̄_H(S) = 0 while F̄_H(x) → α_H/S > 0 as x ↑ S, but x ↦ P(V ≥ x) is left-continuous, so no law has the printed cCDF; the mean computation (EC.13) and the optimal prices [α_H/(1−D), S] need the atom at S.
--   - encoding: the cCDF on its whole domain → compared on x ≥ 0 only; reason: "0 otherwise" would also cover x < 0, where P(V ≥ x) = 1 for V ≥ 0.
--   - encoding: "Eq. (EC.6) with equality" → D·R_PP = log(S)·R_SP; reason: equivalent since D > 0 on [δL, δM].
--   - encoding: "a random variable V" → a probability measure ν on ℝ with Market ν 0; S > 1 as a hypothesis; reason: standing assumptions of §2 and of Theorem 2.
-- source:
--   Elmachtoub, Gupta & Hamilton, The Value of Personalized Pricing, SSRN 3127719 (review version, PDF sha256 635e22eb…), p. ec7 (PDF 39), Lemma EC.3; proof pp. ec8–ec9 (PDF 40–41)

import Mathlib
import Definitions.Def_ValuePersPricing_Deviation_Model

open MeasureTheory Set Filter Topology

namespace ValuePersPricing.Deviation

/-- Lemma EC.3 (p. ec7): tight distributions for `c = 0`, `µ = 1`, `S > 1` (δ's at `M = 1`).
Each part gives a law with the stated cCDF on `x ≥ 0`, scale `S`, coefficient of deviation `D`
and mean `1` that attains (EC.5), (EC.6), (EC.7) respectively with equality.
Corrected: (a) for `D ∈ (0, δ_L]` (at `D = 0` the printed law is the point mass at 1, of scale 1);
(c) the third piece of `F̄_H` is on `(α_H/(1 − D), S]` (the printed `F̄_H(S) = 0` is not
left-continuous, so no law has it). -/
theorem lemma_EC_3 (S : ℝ) (hS : 1 < S) :
    (∀ D ∈ Ioc 0 (deltaL 1 S),
      ∃ ν : Measure ℝ, Market ν 0 ∧ mean ν = 1 ∧ IsScale ν S ∧ coefDev ν = D ∧
        (∀ x : ℝ, 0 ≤ x → tail ν x =
          if x < (lambertWm1 ((D - 1) / Real.exp 1) / (D - 1))⁻¹ then 1
          else if x ≤ 1 then (lambertWm1 ((D - 1) / Real.exp 1) / (D - 1))⁻¹ / x
          else if x ≤ S then D / (Real.log S * x)
          else 0) ∧
        ppProfit ν 0 =
          lambertWm1 ((D - 1) / Real.exp 1) / (D - 1) * spProfit ν 0) ∧
    (∀ D ∈ Icc (deltaL 1 S) (deltaM 1 S),
      ∃ ν : Measure ℝ, Market ν 0 ∧ mean ν = 1 ∧ IsScale ν S ∧ coefDev ν = D ∧
        (∀ x : ℝ, 0 ≤ x → tail ν x =
          if x = 0 then 1
          else if x < Real.exp 1 * S ^ (1 - 1 / D) then
            D / Real.log S / Real.exp 1 * S ^ (1 / D - 1)
          else if x ≤ S then D / Real.log S / x
          else 0) ∧
        coefDev ν * ppProfit ν 0 = Real.log S * spProfit ν 0) ∧
    (∀ D ∈ Icc (deltaM 1 S) (deltaH 1 S),
      ∃ ν : Measure ℝ, Market ν 0 ∧ mean ν = 1 ∧ IsScale ν S ∧ coefDev ν = D ∧
        (∀ x : ℝ, 0 ≤ x → tail ν x =
          if x = 0 then 1
          else if x ≤ (-lambertWm1 (-1 / (Real.exp 1 * S * (1 - D))))⁻¹ / (1 - D) then 1 - D
          else if x ≤ S then (-lambertWm1 (-1 / (Real.exp 1 * S * (1 - D))))⁻¹ / x
          else 0) ∧
        ppProfit ν 0 =
          -lambertWm1 (-1 / (Real.exp 1 * S * (1 - D))) * spProfit ν 0) := by sorry

end ValuePersPricing.Deviation
