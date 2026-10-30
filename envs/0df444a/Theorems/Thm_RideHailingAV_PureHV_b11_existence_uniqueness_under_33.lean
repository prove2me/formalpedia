-- Prove2me | Theorems.Thm_RideHailingAV_PureHV_b11_existence_uniqueness_under_33
-- name    : RideHailingAV.PureHV.b11_existence_uniqueness_under_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:25:43.381488+00:00
-- url     : https://prove2.me/theorems/69c36ead-e367-4c3b-a6ea-cc419db91d12
-- title:
--   App. B.1.1 — under (33), the unique maximal stable equilibrium
-- statement:
--   Consider the model with $a>0$, $0\le r<1$, $t_2>0$, $V>0$, $w_0>0$, $\alpha\ge0$, and a scenario of mass $m>0$. Suppose
--   $$r_i(m/2)>w(\underline n(m/2))\,\underline n(m/2).\qquad(33)$$
--   Then there is a demand rate $d$ with $m/2<d<m$ such that
--
--   1. $d$ is a maximal stable equilibrium;
--   2. $d$ is the only solution of the equilibrium condition (13) in $[m/2,m]$;
--   3. every maximal stable equilibrium equals $d$.
--
--   This is the paper's existence and uniqueness argument for the maximal stable equilibrium; Proposition 1 needs only the weaker Assumption 2 in its form (18).
--
--   Differences from the source:
--   - reading: Definition 1: there is no ε > 0 such that rᵢ(d − ε) < w(n(d − ε))n(d − ε) and rᵢ(d + ε) > w(n(d + ε))n(d + ε) → no ε > 0 with 0 ≤ d − ε and d + ε ≤ m satisfies both inequalities (IsStableHVEquilibrium); reason: keeps the arguments in the demand domain [0, mᵢ] of (3); the maximal stable equilibrium is the largest solution of (13) in [0, mᵢ] under both readings, since beyond mᵢ revenue is negative and cost positive
--   - encoding: equilibrium demand rates → IsHVEquilibrium requires 0 ≤ d ≤ m; reason: (3) defines pᵢ on [0, mᵢ] only
--   - generalization: Assumption 1 (c_v + c_f < w₀ with c_f, c_v > 0, p. 7) → 0 < w₀; reason: the pure-HV market involves no AV and uses Assumption 1 only through w₀ > 0, which Assumption 1 implies, so the statement specializes to the paper's
--   - encoding: the model constants a, t₂ (and V, mᵢ where used) of the ETA function, trip time, value support and demand mass → explicit hypotheses 0 < a, 0 < t₂ (0 < V, 0 < m where used); reason: implicit in the model: ã > 0 is stated on p. 12 and ã > 0 iff a > 0; t₂ is a trip time; V is the top of the value support [0, V]; (3) divides by mᵢ
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), Appendix B.1.1, p. 42 (unnumbered; eqs. (33), (35)–(38))

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market
import Definitions.Def_RideHailingAV_PureHV_IsMaxStableHVEquilibrium

namespace RideHailingAV.PureHV

/-- **App. B.1.1 — under (33), the unique maximal stable equilibrium.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), Appendix B.1.1,
p. 42 (unnumbered): "We prove that under Eq. (33), there is precisely one solution that satisfies
equilibrium condition (13) in the interval `d_HV ∈ [m_i/2, m_i]`; moreover, it is a stable
equilibrium (Definition 1). Therefore, this solution is the unique maximal stable equilibrium."
Here (33) is `r_i(m_i/2) > w(n(m_i/2))n(m_i/2)`.

Under the model's standing conditions and `m > 0`, if (33) holds then there is `d` with
`m/2 < d < m` (the root lies in the open interval, eq. (38)) such that `d` is a maximal stable
equilibrium, `d` is the only solution of (13) in `[m/2, m]`, and every maximal stable
equilibrium equals `d`. -/
theorem b11_existence_uniqueness_under_33 (M : Market) (ha : 0 < M.a) (hr0 : 0 ≤ M.r)
    (hr1 : M.r < 1) (ht2 : 0 < M.t2) (hV : 0 < M.V) (hw0 : 0 < M.w0) (hα : 0 ≤ M.α)
    (m : ℝ) (hm : 0 < m) (h33 : laborCost M (m / 2) < revenue M m (m / 2)) :
    ∃ d : ℝ, m / 2 < d ∧ d < m ∧ IsMaxStableHVEquilibrium M m d ∧
      (∀ d' ∈ Set.Icc (m / 2) m, revenue M m d' = laborCost M d' → d' = d) ∧
      ∀ d', IsMaxStableHVEquilibrium M m d' → d' = d := by sorry

end RideHailingAV.PureHV
