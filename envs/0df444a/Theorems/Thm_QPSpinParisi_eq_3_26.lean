-- Prove2me | Theorems.Thm_QPSpinParisi_eq_3_26
-- name    : QPSpinParisi.eq_3_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:19:33.76088+00:00
-- url     : https://prove2.me/theorems/4da26715-70b2-458b-9140-bc0abf392651
-- title:
--   Eq. (3.26) — $\limsup_{\beta\to\infty}A_\xi(\beta)/\beta\le\inf_{\gamma\in\mathcal U}P_\xi(\gamma)$
-- statement:
--   The upper bound of the zero-temperature limit:
--   $$\limsup_{\beta\to\infty}\frac{A_\xi(\beta)}\beta\le\inf_{\gamma\in\mathcal U}P_\xi(\gamma).\tag{3.26}$$
--   It covers unbounded $\gamma\in\mathcal U$. Together with the lower bound it gives (3.25).
--
--   Differences from the source:
--   - generalization: one Brownian motion $B$ on an unnamed space → every `BrownianNoise`, on every probability space; reason: the source's $B$ is one such object, and `exists_noise` makes the statement non-vacuous
--   - generalization: $Y_n$ built as $\sum_pc_pY_{n,p}$ → every centered Gaussian field with covariance $n\xi(q(s,t))$ and continuous paths; reason: only the covariance is used; the source's field is one such field, and `exists_overlapField` makes the statement non-vacuous
--   - encoding: $\limsup$ / $\liminf$ → an eventual bound for each $\varepsilon>0$; reason: the same statement, without default values of a real $\limsup$
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Eq. (3.26), p.20 (PDF p.20)

import Mathlib
import Definitions.Def_QPSpinParisi_MixHyp
import Definitions.Def_QPSpinParisi_IsFreeEnergyLimit
import Definitions.Def_QPSpinParisi_Pf
import Definitions.Def_QPSpinParisi_USet

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Eq. (3.26), p.20, PDF p.20: `limsup_{β→∞} A_ξ(β)/β ≤ inf_{γ ∈ U} P_ξ(γ)`.

**Formalization Note** The limsup bound is written as an eventual bound for each `γ ∈ U` and `ε > 0`, which avoids the default values of a
real `limsup`. `γ` may be unbounded. -/
theorem eq_3_26 (c : ℕ → ℝ) (hc : MixHyp c) (W : BrownianNoise c) (A : ℝ → ℝ)
    (hA : IsFreeEnergyLimit c A) (γ : Ico (0 : ℝ) 1 → ℝ) (hγ : γ ∈ USet) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ β in atTop, A β / β ≤ Pf W γ + ε := by sorry

end QPSpinParisi
