-- Prove2me | Theorems.Thm_PrivInfoHier_Main_eq_B_6_B_7
-- name    : PrivInfoHier.Main.eq_B_6_B_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:14:44.41109+00:00
-- url     : https://prove2.me/theorems/b0d6be4f-fc2a-485b-ab06-354a49c16f5f
-- title:
--   §B.1, Eqs. (B.6)–(B.7) — the stopped divergence of a valid spec-level filter on the B.1 process
-- statement:
--   Let $\theta,\delta\in(0,1)$, $\varepsilon>0$, and consider the App. B.1 process. Let $T_S$ be an $(\varepsilon,\delta)$-valid spec-level filter, with internal randomness $Z$ of any law, let $\mathcal A$ be a request strategy, $x\sim x'$ with $x\ne x'$, and $\mu_t=P_x(T_S=t)$. Then $\delta^+_{(T_S)}\le\delta$ by Definition 2.2, and
--   $$\delta^+_{(T_S)}=\mathbb E_x\Big[\big(1-e^{\varepsilon-L^{(T_S)}}\big)_+\Big]=\sum_{t=1}^\infty\mu_t\,\mathbb E_x\Big[\big(1-e^{\varepsilon-L^{(t)}}\big)_+\,\Big|\,T_S=t\Big]=\sum_{t=1}^\infty\mu_t\,\delta^+_t$$
--   $$=\mathbb E_{T_S\sim\mu}\big[1-(1-\theta)^{T_S-1}\big]\le\delta.$$
--   The statement is the conjunction of $\delta^+_{(T_S)}\le\delta$ and of each relation in this chain.
--
--   Differences from the source:
--   - generalization: fixed requests → every request space and every request strategy; reason: the B.1 rules ignore requests; App. B says the arguments hold uniformly.
--   - generalization: a spec-level filter with a finite horizon → any spec-level filter, no horizon assumed; reason: the argument never uses the horizon; filters with a horizon are a special case.
--   - reading: $L_i=\infty$ "for all $x\sim x'$" → the hypothesis $x\neq x'$; reason: the unsafe mechanism separates $x$ from $x'$ only when they differ.
--   - reading: $\mathbb E_{T_S\sim\mu}[\,\cdot\,]$ with $\mu=(\mu_t)_{t\ge1}$ → $\sum_{t\ge1}\mu_t(\cdot)$; reason: $\mu$ is indexed by $t\ge1$ (p. 18), and at $T_S=0$ the stopped divergence contributes $0$.
--   - encoding: $\mu_t\,\mathbb E_x[\,\cdot\mid T_S=t]$ → $\int_{\{T_S=t\}}(\cdot)\,dP_x$; reason: equal when $\mu_t>0$, and avoids conditioning on a null event.
--   - encoding: $e^{\varepsilon-L}$, $(\cdot)_+$ and the series → `ofReal (exp ε) * expNegCumLoss`, truncated subtraction and `tsum` in $[0,\infty]$; reason: all terms are nonnegative.
-- source:
--   Taylor, Vippathalla, Coon, An Information Hierarchy of Privacy Filters and Odometers, arXiv:2611.03130 (held version, sha256 77181933…), pp. 18–19 (PDF 20–21), App. B.1, Eqs. (B.6)–(B.7)

import Mathlib
import Definitions.Def_PrivInfoHier_Main_Model
import Definitions.Def_PrivInfoHier_Main_Filter
import Definitions.Def_PrivInfoHier_Main_B1

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PrivInfoHier.Main

/-- App. B.1, (B.6)–(B.7): for an `(ε, δ)`-valid spec-level filter `T_S` on the B.1 process, every
request strategy and neighbouring `x ∼ x′` with `x ≠ x′`, writing `μ_t = P_x(T_S = t)`:
`δ⁺_{(T_S)} ≤ δ`, and
`δ⁺_{(T_S)} = E_x[(1 − e^{ε − L^{(T)}})_+] = Σ_{t ≥ 1} μ_t E_x[(1 − e^{ε − L^{(t)}})_+ | T_S = t]
 = Σ_{t ≥ 1} μ_t δ⁺_t = Σ_{t ≥ 1} μ_t (1 − (1 − θ)^{t−1}) ≤ δ`. -/
theorem eq_B_6_B_7 (𝒳 ℛ : Type) [MeasurableSpace ℛ] (nb : 𝒳 → 𝒳 → Prop)
    (θ : Set.Ioo (0 : ℝ) 1) (ε δ : ℝ) (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (𝒵 : Type) [MeasurableSpace 𝒵] (μZ : Measure 𝒵) [IsProbabilityMeasure μZ]
    (T : 𝒵 × Path ℛ (B1Out 𝒳) → ℕ) (hspec : IsSpecLevel T)
    (hvalid : IsValid (b1Process 𝒳 ℛ θ) nb ε δ μZ T)
    (A : RequestStrategy ℛ (B1Out 𝒳)) (x x' : 𝒳) (hnb : nb x x') (hxx' : x ≠ x') :
    deltaPlusStopped (b1Process 𝒳 ℛ θ) A x x' ε μZ T ≤ ENNReal.ofReal δ ∧
    deltaPlusStopped (b1Process 𝒳 ℛ θ) A x x' ε μZ T
      = ∫⁻ ω, (1 - ENNReal.ofReal (Real.exp ε) *
            expNegCumLoss (b1Process 𝒳 ℛ θ) x x' (T ω) ω.2) ∂(filterLaw (b1Process 𝒳 ℛ θ) A x μZ) ∧
    ∫⁻ ω, (1 - ENNReal.ofReal (Real.exp ε) *
            expNegCumLoss (b1Process 𝒳 ℛ θ) x x' (T ω) ω.2) ∂(filterLaw (b1Process 𝒳 ℛ θ) A x μZ)
      = ∑' t : ℕ, ∫⁻ ω in {ω | T ω = t + 1}, (1 - ENNReal.ofReal (Real.exp ε) *
            expNegCumLoss (b1Process 𝒳 ℛ θ) x x' (t + 1) ω.2) ∂(filterLaw (b1Process 𝒳 ℛ θ) A x μZ) ∧
    ∑' t : ℕ, ∫⁻ ω in {ω | T ω = t + 1}, (1 - ENNReal.ofReal (Real.exp ε) *
            expNegCumLoss (b1Process 𝒳 ℛ θ) x x' (t + 1) ω.2) ∂(filterLaw (b1Process 𝒳 ℛ θ) A x μZ)
      = ∑' t : ℕ, filterLaw (b1Process 𝒳 ℛ θ) A x μZ {ω | T ω = t + 1} *
          deltaPlus (b1Process 𝒳 ℛ θ) A x x' ε (t + 1) ∧
    ∑' t : ℕ, filterLaw (b1Process 𝒳 ℛ θ) A x μZ {ω | T ω = t + 1} *
          deltaPlus (b1Process 𝒳 ℛ θ) A x x' ε (t + 1)
      = ∑' t : ℕ, filterLaw (b1Process 𝒳 ℛ θ) A x μZ {ω | T ω = t + 1} *
          ENNReal.ofReal (1 - (1 - θ.1) ^ t) ∧
    ∑' t : ℕ, filterLaw (b1Process 𝒳 ℛ θ) A x μZ {ω | T ω = t + 1} *
          ENNReal.ofReal (1 - (1 - θ.1) ^ t) ≤ ENNReal.ofReal δ := by sorry

end PrivInfoHier.Main
