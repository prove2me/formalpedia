-- Prove2me | Theorems.Thm_TaylorInv_theorem_1
-- name    : TaylorInv.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:51.612066+00:00
-- url     : https://prove2.me/theorems/bf314749-f2b5-4abc-9a46-c730a083762f
-- title:
--   Theorem 1 (corrected: $\underline h>0$) — the TA policy is asymptotically optimal in the number of retailers
-- statement:
--   Fix the number of features $P$ and bounds $0\le h_0\le\underline h$, $0<\underline h\le\bar h\le\bar b$, $0<\underline\ell\le\bar u$ and $\bar D,\bar\epsilon,\bar B,\bar M,\bar\sigma$. There are constants $K$ and $c_1>0$, depending only on these, such that for every $J\ge1$ and every one-warehouse, $J$-retailer system satisfying Assumptions 1–3 within these bounds (warehouse cost $h_0$, $\underline h\le h'_j\le\bar h\le b_j\le\bar b$, $\underline\ell\le\ell_j$, $u_j\le\bar u$), with $\tilde z_0$ the TA order (17), $\tilde z_j=\tilde z_j(\tilde z_0,x)$ the TA allocation and $s_j^l$ the local base stocks:
--
--   1. **(i)** $C_{OPT}>0$ and
--   $$
--   C_{TA}-C_{OPT}\le\frac KJ\,C_{OPT},\qquad \tilde z_0-\mathbb E_x\Big[\sum_{j=1}^Js_j^l\Big]=0,\qquad \mathbb E_x\big[|\tilde z_j-s_j^l|\big]\le K\ \text{ for every }j,
--   $$
--   the expectations being of integrable functions;
--   2. **(ii)** almost surely $C_{OPT}(x)>0$, where $C_{OPT}(x)$ denotes $h_0z_0+G(z_0\mid x)$ at any order $z_0\ge0$; for every $0<\delta<1-2e^{-c_1J}$, with probability at least $1-2e^{-c_1J}-\delta$,
--   $$
--   \big(C_{TA}(x)-C_{OPT}(x)\big)^+\le K\Big(\frac{\ln(2/\delta)}J+\sqrt{\frac{\ln(2/\delta)}J}\Big)\,C_{OPT}(x)\quad\text{at every order }z_0\ge0;
--   $$
--   for every $0<\delta<1$, with probability at least $1-\delta$, $|\tilde z_0-\sum_js_j^l|\le K\sqrt{J\ln(2/\delta)}$; and for every $0<\delta<1-2e^{-c_1J}$, with probability at least $1-2e^{-c_1J}-\delta$, $|\tilde z_j-s_j^l|\le K\sqrt{\ln(2/\delta)/J}$ for all $j$.
--
--   The relative optimality gap of the TA policy, which orders the expected sum of the retailers' newsvendor quantiles and allocates by a second-order Taylor expansion, thus vanishes at rate $1/J$, in expectation and with high probability.
--
--   **Formalization Note** Ratios are written as products, with the positivity of the denominators stated. The probabilities are upper bounds on the (outer) measure of the failure events.
--
--   Differences from the source:
--   - correction: $0\le h_0\le\underline h$ → additionally $0<\underline h$; reason: the theorem is false at $\underline h=0$: $P=1$, $x_j$ uniform on $\{\pm1\}$, $\beta_j=1$, $\gamma_j=2$, $\epsilon_j$ uniform on $[-1,1]$, $h_0=0$, $h'_1=1$, $h'_j=0$ ($j\ge2$), $b_j=1$ give $C_{OPT}=1/2$ and $C_{TA}\ge1/2+1/9$, so $(C_{TA}-C_{OPT})/C_{OPT}\ge2/9$ for every $J\ge2$
--   - reading: $O(\cdot)$ and the constant $c_1$ → $\exists K,c_1$ depending only on $P$ and the bounds $h_0,\underline h,\bar h,\bar b,\underline\ell,\bar u,\bar D,\bar\epsilon,\bar B,\bar M,\bar\sigma$, for every $J\ge1$ and every system within them; reason: the proof's constants $\alpha,\underline p,\underline t,\bar t,\underline\ell,\underline h$ are called constants by the paper; uniformity in $J$ is the content of $O(\cdot)$, and every $J\ge1$ is no stronger than $J$ large
--   - reading: (ii) "for any given feature $x$ … with probability" → probabilities over the features; the bound on $|\tilde z_j-s_j^l|$ for all $j$ simultaneously; "with probability $1-\delta$" for every $\delta\in(0,1)$; reason: for a fixed $x$ nothing is random; the proof's event $\mathscr B$ (p.OA11) is a set of features; the simultaneous reading is the stronger one
--   - reading: $C_j$ of (4), whose term $-h_0D_j$ the paper omits in its analysis (p.8) → the period cost (2), which equals (3)–(4) with the term kept; reason: with the term omitted the cost differences are unchanged and $C_{OPT}$ only grows; the paper's own display of $C_{AF}(x)$ on p.OA10 is the (2) form
--   - generalization: $C_{OPT}(x)$ at the optimal order $z_0^*$ → $h_0z_0+G(z_0\mid x)$ at every order $z_0\ge0$ simultaneously; reason: specializes to $z_0=z_0^*$ and needs no existence of $z_0^*$
--   - encoding: $z_j>0$, $z_0>0$ in (5) and (14) → $z_j\ge0$, $z_0\ge0$; reason: (6) uses $z_j\ge0$; the argmin of (14) has zero coordinates in case (16); the infimum (5) is unchanged
--   - encoding: the ratios $(C_{TA}-C_{OPT})/C_{OPT}$ and $(C_{TA}(x)-C_{OPT}(x))^+/C_{OPT}(x)$ → products, with $0<C_{OPT}$ and $0<C_{OPT}(x)$ stated; reason: the paper's ratios presuppose positive denominators
--   - encoding: the expectations $\mathbb E_x[C_{TA}(x)]$, $\mathbb E_x|\tilde z_j-s_j^l|$ → integrability stated with the bound; reason: the paper's expectations presuppose it
--   - encoding: noise $\epsilon_j$ independent of $x_j$; $C_j$ and the retailer costs are conditional expectations $\mathbb E_{\epsilon_j}[\cdot\mid x_j]$ → the noise enters through its density $f_j$ on $[lo_j,hi_j]$, the costs are integrals against $f_j$; the features are random variables on $(\Omega,\mu)$; reason: with $\epsilon_j$ independent of $x_j$ the conditional expectation is this integral; same instances
--   - encoding: $\tilde z(z_0,x)=\arg\min$ of (14), $C_{OPT}=\min_{z_0}$ → `Classical.epsilon` choice of a minimizer; $C_{OPT}$ as an infimum over $z_0\ge0$; reason: the minimizer of (14) is unique (Proposition 2); the infimum equals the minimum when it is attained
--   - encoding: retailers $j\in[J]^+$ and features $p\in[P]^+$ → `Fin J` and `Fin P` (0-based); reason: Lean convention; same instances
-- source:
--   Huang, Shang, Yang & Zhou, Taylor Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature Information, SSRN 3993516 (Jan 29 2023), https://ssrn.com/abstract=3993516, Theorem 1, p.16; proof pp.OA5–OA12

import Mathlib
import Definitions.Def_TaylorInv_Policies
import Definitions.Def_TaylorInv_InClass

open MeasureTheory ProbabilityTheory

universe u

namespace TaylorInv

/-- Theorem 1, asymptotic optimality of the TA policy (Huang, Shang, Yang & Zhou, *Taylor
Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature
Information*, SSRN 3993516 (Jan 29 2023), Theorem 1, p.16), corrected by `0 < h̲`.

Fix `P` and the bounds `0 ≤ h₀ ≤ h̲`, `0 < h̲ ≤ h̄ ≤ b̄`, `0 < ℓ̲ ≤ ū`, `D̄, ϵ̄, B̄, M̄, σ̄`. There are
constants `K` and `c₁ > 0`, depending only on these, such that for every `J ≥ 1` and every
`J`-retailer system satisfying Assumptions 1–3 within these bounds (`Model.InClass`):

(i) `0 < C_OPT` and `C_TA − C_OPT ≤ (K/J) C_OPT`; `z̃₀ − 𝔼_x[∑_j s_j^l] = 0`; and for every `j`,
`𝔼_x|z̃_j − s_j^l| ≤ K` (with the integrands integrable);

(ii) almost surely `C_OPT(x) > 0` at every order `z₀ ≥ 0`; for every `0 < δ < 1 − 2e^{−c₁J}`, outside
an event of probability at most `2e^{−c₁J} + δ`,
`(C_TA(x) − C_OPT(x))⁺ ≤ K (J⁻¹ ln(2/δ) + √(J⁻¹ ln(2/δ))) C_OPT(x)` at every order `z₀ ≥ 0`;
for every `0 < δ < 1`, `|z̃₀ − ∑_j s_j^l| ≤ K √(J ln(2/δ))` outside an event of probability at
most `δ`; and for every `0 < δ < 1 − 2e^{−c₁J}`, `|z̃_j − s_j^l| ≤ K √(J⁻¹ ln(2/δ))` for all `j`
outside an event of probability at most `2e^{−c₁J} + δ`.

**Formalization Note** `C_OPT(x)` at the order `z₀` is `optCostGiven z₀ ω = h₀ z₀ + G(z₀ | x)`; the
paper's `C_OPT(x)` is the case `z₀ = z₀*`. Ratios are written as products, and the probabilities as
upper bounds on the (outer) measure of the failure events. `z̃_j` is `taAlloc (taOrder μ) ω j`. -/
theorem theorem_1 (P : ℕ) (h₀ hlow hbar bbar ℓlow ubar Dbar ϵbar Bbar Mbar σbar : ℝ)
    (hh₀ : 0 ≤ h₀) (hh₀low : h₀ ≤ hlow) (hlow_pos : 0 < hlow) (hlowbar : hlow ≤ hbar)
    (hbarb : hbar ≤ bbar) (hℓlow : 0 < ℓlow) (hℓu : ℓlow ≤ ubar) :
    ∃ K c₁ : ℝ, 0 < c₁ ∧
      ∀ (J : ℕ), 1 ≤ J → ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (M : Model J P Ω), M.InClass μ h₀ hlow hbar bbar ℓlow ubar Dbar ϵbar Bbar Mbar σbar →
        -- (i)
        (0 < M.costOPT μ ∧ Integrable (M.costTAGiven μ) μ ∧
          M.costTA μ - M.costOPT μ ≤ K / J * M.costOPT μ) ∧
        M.taOrder μ - ∫ ω, ∑ j, M.baseStock j ω ∂μ = 0 ∧
        (∀ j, Integrable (fun ω => |M.taAlloc (M.taOrder μ) ω j - M.baseStock j ω|) μ ∧
          ∫ ω, |M.taAlloc (M.taOrder μ) ω j - M.baseStock j ω| ∂μ ≤ K) ∧
        -- (ii)
        (∀ᵐ ω ∂μ, ∀ z₀, 0 ≤ z₀ → 0 < M.optCostGiven z₀ ω) ∧
        (∀ δ : ℝ, 0 < δ → δ < 1 - 2 * Real.exp (-c₁ * J) →
          μ {ω | ∃ z₀, 0 ≤ z₀ ∧ ¬ (max (M.costTAGiven μ ω - M.optCostGiven z₀ ω) 0
              ≤ K * ((J : ℝ)⁻¹ * Real.log (2 / δ) + Real.sqrt ((J : ℝ)⁻¹ * Real.log (2 / δ)))
                * M.optCostGiven z₀ ω)}
            ≤ ENNReal.ofReal (2 * Real.exp (-c₁ * J) + δ)) ∧
        (∀ δ : ℝ, 0 < δ → δ < 1 →
          μ {ω | K * Real.sqrt (J * Real.log (2 / δ)) < |M.taOrder μ - ∑ j, M.baseStock j ω|}
            ≤ ENNReal.ofReal δ) ∧
        (∀ δ : ℝ, 0 < δ → δ < 1 - 2 * Real.exp (-c₁ * J) →
          μ {ω | ∃ j, K * Real.sqrt ((J : ℝ)⁻¹ * Real.log (2 / δ))
              < |M.taAlloc (M.taOrder μ) ω j - M.baseStock j ω|}
            ≤ ENNReal.ofReal (2 * Real.exp (-c₁ * J) + δ)) := by sorry

end TaylorInv
