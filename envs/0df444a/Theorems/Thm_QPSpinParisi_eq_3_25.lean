-- Prove2me | Theorems.Thm_QPSpinParisi_eq_3_25
-- name    : QPSpinParisi.eq_3_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:19:04.269215+00:00
-- url     : https://prove2.me/theorems/7d3521d1-37cf-4803-9b19-9b330510de88
-- title:
--   Eq. (3.25) — $\lim_{\beta\to\infty}A_\xi(\beta)/\beta=\inf_{\gamma\in\mathcal U}P_\xi(\gamma)$
-- statement:
--   The zero-temperature limit of the free energy:
--   $$\lim_{\beta\to\infty}\frac{A_\xi(\beta)}\beta=\inf_{\gamma\in\mathcal U}P_\xi(\gamma).\tag{3.25}$$
--   The infimum is attained. With Lemma 3.3 this identifies the limit of the ground-state energy with the infimum of the Parisi functional.
--
--   Differences from the source:
--   - generalization: one Brownian motion $B$ on an unnamed space → every `BrownianNoise`, on every probability space; reason: the source's $B$ is one such object, and `exists_noise` makes the statement non-vacuous
--   - generalization: $Y_n$ built as $\sum_pc_pY_{n,p}$ → every centered Gaussian field with covariance $n\xi(q(s,t))$ and continuous paths; reason: only the covariance is used; the source's field is one such field, and `exists_overlapField` makes the statement non-vacuous
--   - reading: $\inf_{\gamma\in\mathcal U}$ → the infimum is attained (`IsLeast`); reason: p.23 proves "$=P_\xi(\gamma)\ge\inf$" with a $\gamma\in\mathcal U$, and p.4 states existence of the minimizer
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Eq. (3.25), stated p.19 (PDF p.19), proved p.23 (PDF p.23)

import Mathlib
import Definitions.Def_QPSpinParisi_MixHyp
import Definitions.Def_QPSpinParisi_IsFreeEnergyLimit
import Definitions.Def_QPSpinParisi_Pf
import Definitions.Def_QPSpinParisi_USet

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Eq. (3.25), stated p.19, PDF p.19, proved p.23, PDF p.23: `lim_{β→∞} A_ξ(β)/β = inf_{γ ∈ U} P_ξ(γ)`, with the infimum attained
("`= P_ξ(γ) ≥ inf`", p.23). -/
theorem eq_3_25 (c : ℕ → ℝ) (hc : MixHyp c) (W : BrownianNoise c) (A : ℝ → ℝ)
    (hA : IsFreeEnergyLimit c A) :
    ∃ L : ℝ, IsLeast (Pf W '' USet) L ∧ Tendsto (fun β => A β / β) atTop (𝓝 L) := by sorry

end QPSpinParisi
