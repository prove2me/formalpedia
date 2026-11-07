-- Prove2me | Theorems.Thm_PFRelease_fact_B_4
-- name    : PFRelease.fact_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:46:58.179703+00:00
-- url     : https://prove2.me/theorems/dc031995-acf8-4a32-8aa7-eb9ec9e6ac51
-- title:
--   Fact B.4 — failure-event accounting
-- statement:
--   Let $\varepsilon\ge0$ and $\delta_1,\delta_2\in[0,1]$. Let $X_0,X_1$ be random variables and $E_0,E_1$ events with $\Pr[X_z\in E_z]>0$ for both $z\in\{0,1\}$. If
--   $$
--   (X_0\mid X_0\in E_0)\approx_{\varepsilon,\delta_1}(X_1\mid X_1\in E_1)
--   \quad\text{and}\quad \Pr[X_z\in E_z]\ge1-\delta_2\ \text{ for both } z,
--   $$
--   then $X_0\approx_{\varepsilon,\delta_1+\delta_2}X_1$.
--
--   It accounts for the event that the noisy cap of the filter exceeds its deterministic bound.
--
--   **Formalization Note** The random variables are represented by their laws (probability measures on a common space); conditioning is `ProbabilityTheory.cond`.
--
--   Differences from the source:
--   - encoding: random variables $X_0,X_1$ and events $E_0,E_1$ → probability measures $\mu_0,\mu_1$ on a common measurable space and measurable sets $E_0,E_1$; conditional laws by `ProbabilityTheory.cond`; reason: the statement concerns only the laws
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Fact B.4, p.32 (PDF p.34)

import Mathlib
import Definitions.Def_PFRelease_Indist

open MeasureTheory

namespace PFRelease

/-- **Fact B.4 (Failure-event accounting, Fact 2.5 in the full version of [CKM+21])** (Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via
Private Filtering*, arXiv:2610.40654 (held version, sha256 e1d516b3…),
Fact B.4, p.32 = PDF p.34). Given `ε ≥ 0`, `δ₁, δ₂ ∈ [0, 1]`, random variables `X₀, X₁` and events
`E₀, E₁` with `Pr[X_z ∈ E_z] > 0` for both `z`, if `(X₀ | X₀ ∈ E₀) ≈_{ε,δ₁} (X₁ | X₁ ∈ E₁)` and
`Pr[X_z ∈ E_z] ≥ 1 − δ₂` for both `z`, then `X₀ ≈_{ε,δ₁+δ₂} X₁`.

**Formalization Note** `X₀, X₁` are represented by their laws `μ₀, μ₁` (probability measures on a
common space), the events by measurable sets, and the conditional laws by `ProbabilityTheory.cond`. -/
theorem fact_B_4 {Ω : Type*} [MeasurableSpace Ω] (ε δ₁ δ₂ : ℝ) (hε : 0 ≤ ε) (hδ₁0 : 0 ≤ δ₁)
    (hδ₁1 : δ₁ ≤ 1) (hδ₂0 : 0 ≤ δ₂) (hδ₂1 : δ₂ ≤ 1) (μ₀ μ₁ : Measure Ω)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] (E₀ E₁ : Set Ω)
    (hE₀ : MeasurableSet E₀) (hE₁ : MeasurableSet E₁) (hpos₀ : 0 < μ₀ E₀) (hpos₁ : 0 < μ₁ E₁)
    (hcond : Indist (ProbabilityTheory.cond μ₀ E₀) (ProbabilityTheory.cond μ₁ E₁) ε δ₁)
    (hbig₀ : ENNReal.ofReal (1 - δ₂) ≤ μ₀ E₀) (hbig₁ : ENNReal.ofReal (1 - δ₂) ≤ μ₁ E₁) :
    Indist μ₀ μ₁ ε (δ₁ + δ₂) := by sorry

end PFRelease
