-- Prove2me | Theorems.Thm_RideHailingAV_PureHV_b11_gap_strictAntiOn
-- name    : RideHailingAV.PureHV.b11_gap_strictAntiOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:24:45.614177+00:00
-- url     : https://prove2.me/theorems/bf811388-84b3-407a-b3c4-5ea4f55aa024
-- title:
--   App. B.1.1 — the gap $r_i-w(\underline n)\underline n$ is strictly decreasing on $[m_i/2,m_i]$
-- statement:
--   Consider the model with $a>0$, $0\le r<1$, $t_2>0$, $V>0$, $w_0>0$, $\alpha\ge0$, and a scenario of potential demand mass $m>0$. Then the function
--   $$d\ \longmapsto\ r_i(d)-w(\underline n(d))\,\underline n(d)$$
--   is strictly decreasing on $[m/2,m]$. In particular there is at most one $d\in[m/2,m]$ at which it vanishes, i.e. at most one solution of the equilibrium condition (13) in $[m/2,m]$.
--
--   This is the uniqueness half of the existence-and-uniqueness argument of Appendix B.1.1.
--
--   Differences from the source:
--   - reading: there is only one d ∈ [mᵢ/2, mᵢ] with rᵢ(d) − w(n(d))n(d) = 0 → at most one such d; reason: existence is a separate step under (33) (eq. (38)); without (33) there may be no zero in [mᵢ/2, mᵢ]
--   - generalization: Assumption 1 (c_v + c_f < w₀ with c_f, c_v > 0, p. 7) → 0 < w₀; reason: the pure-HV market involves no AV and uses Assumption 1 only through w₀ > 0, which Assumption 1 implies, so the statement specializes to the paper's
--   - encoding: the model constants a, t₂ (and V, mᵢ where used) of the ETA function, trip time, value support and demand mass → explicit hypotheses 0 < a, 0 < t₂ (0 < V, 0 < m where used); reason: implicit in the model: ã > 0 is stated on p. 12 and ã > 0 iff a > 0; t₂ is a trip time; V is the top of the value support [0, V]; (3) divides by mᵢ
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), Appendix B.1.1, p. 43 (unnumbered)

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market
import Definitions.Def_RideHailingAV_PureHV_revenue
import Definitions.Def_RideHailingAV_PureHV_laborCost

namespace RideHailingAV.PureHV

/-- **App. B.1.1 — the gap `r_i − w(n)n` is strictly decreasing on `[m_i/2, m_i]`.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023),
Appendix B.1.1, p. 43 (unnumbered): "the function `r_i(d_HV) − w(n(d_HV))n(d_HV)` is strictly
decreasing for `d_HV ∈ [m_i/2, m_i]`, implying that there is only one `d_HV ∈ [m_i/2, m_i]` such that
`r_i(d_HV) − w(n(d_HV))n(d_HV) = 0`."

Under the model's standing conditions (`a, t₂, V, w₀ > 0`, `0 ≤ r < 1`, `α ≥ 0`) and `m > 0`:
the gap is strictly decreasing on `[m/2, m]`, and it has at most one zero there. -/
theorem b11_gap_strictAntiOn (M : Market) (ha : 0 < M.a) (hr0 : 0 ≤ M.r) (hr1 : M.r < 1)
    (ht2 : 0 < M.t2) (hV : 0 < M.V) (hw0 : 0 < M.w0) (hα : 0 ≤ M.α) (m : ℝ) (hm : 0 < m) :
    StrictAntiOn (fun d => revenue M m d - laborCost M d) (Set.Icc (m / 2) m) ∧
      ∀ d₁ ∈ Set.Icc (m / 2) m, ∀ d₂ ∈ Set.Icc (m / 2) m,
        revenue M m d₁ = laborCost M d₁ → revenue M m d₂ = laborCost M d₂ → d₁ = d₂ := by sorry

end RideHailingAV.PureHV
