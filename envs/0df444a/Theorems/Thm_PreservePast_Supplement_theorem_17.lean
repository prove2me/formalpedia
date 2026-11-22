-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_17
-- name    : PreservePast.Supplement.theorem_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:41:26.100815+00:00
-- url     : https://prove2.me/theorems/ad6232aa-19b4-4c3f-b532-e1190196531f
-- title:
--   Theorem 17 — weak-supercritical retention frontier
-- statement:
--   In the nearest-of-$k$ experiment on the cube, fix $c>1$. As $k\to\infty$, let $d\ge k^{0.1}$ and $\rho^2d=2c\ln k$, and put
--   $$r(c)=1-h_2\Big(\frac{1-c^{-1/2}}2\Big).$$
--   Every sequence of arbitrary joint randomized protocols satisfies
--   $$\frac{I(X;M\mid R)}{kd}\ge r(c)\,S-o(1).$$
--   For every fixed $0<S<1$, both costs satisfy
--   $$C(S)/(kd)=S\,r(c)+o(1),\qquad C\in\{I_{\min},B_{\min}\}.$$
--   There is also a finite-width sequence of success tending to one and cost $(r(c)+o(1))kd$.
--
--   Above the critical signal, the retained information per record is the classical compressed-identification coefficient, for arbitrary joint messages.
--
--   Differences from the source:
--   - encoding: o(1) as k → ∞ (resp. d → ∞), for every sequence of protocols → a sequence e → 0 valid for all admissible parameters and all protocols at each index; reason: equivalent to the statement for every sequence of parameters and protocols
--   - encoding: C(S)/(kd) = S·r + o(1) for C ∈ {I_min, B_min} → every protocol of success ≥ S has information and width ≥ (S·r − e)kd, and from some index on a protocol of success ≥ S has width and information ≤ (S·r + e)kd; reason: two-part form of a least cost; avoids junk values of infima
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 17, p.62 (PDF p.64), eqs. (227)–(228); Definition 1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_PreservePast_Supplement_IdProtocol

open MeasureTheory Filter Topology

namespace PreservePast.Supplement

/-- **Theorem 17 (Weak-supercritical retention frontier).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Theorem 17, p.62 (PDF p.64),
eqs. (227)–(228); the experiment is Definition 1, p.10 (PDF p.12).

Fix `c > 1`. As `k → ∞` with `d ≥ k^{0.1}` and `ρ²d = 2c ln k`, and
`r(c) = 1 − h₂((1 − c^{−1/2})/2)`: (227) every protocol has `I(X; M | R)/(kd) ≥ r(c)S − o(1)`;
(228) for every fixed `0 < S < 1`, `C(S)/(kd) = S r(c) + o(1)` for `C ∈ {I_min, B_min}`; and
there is a finite-width sequence of success tending to one and cost `(r(c) + o(1))kd`.

**Formalization Note.** Each `o(1)` is a sequence `e_k → 0` valid for all admissible
`(d, ρ)` at each `k` (equivalent to the statement for every sequence of parameters and
protocols). (228) is stated in two parts for each cost: the lower bound for every protocol of
success `≥ S` (for `I_min` this is (227); for `B_min`, every such protocol whose message fits
`B` bits has `B ≥ (S r(c) − e_k)kd`), and, for `k` beyond a threshold, a protocol of success
`≥ S` whose message fits `B ≤ (S r(c) + e_k)kd` bits and whose information is at most
`(S r(c) + e_k)kd`. Information is compared through `ENNReal.ofReal`. -/
theorem theorem_17 :
    ∀ c : ℝ, 1 < c →
      (∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
        ∀ (k d : ℕ) (ρ : ℝ), 2 ≤ k → (k : ℝ) ^ (0.1 : ℝ) ≤ d → 0 < ρ → ρ < 1 →
          ρ ^ 2 * d = 2 * c * Real.log k →
          (∀ π : IdProtocol k d,
            ENNReal.ofReal (((1 - h2 ((1 - c ^ (-(1 / 2 : ℝ))) / 2)) * π.success ρ - e k) *
              (k * d)) ≤ π.info) ∧
          ∃ (π : IdProtocol k d) (B : ℕ), π.HasWidth B ∧ 1 - e k ≤ π.success ρ ∧
            (B : ℝ) ≤ ((1 - h2 ((1 - c ^ (-(1 / 2 : ℝ))) / 2)) + e k) * (k * d)) ∧
      ∀ S : ℝ, 0 < S → S < 1 → ∃ (e : ℕ → ℝ) (k₀ : ℕ), Tendsto e atTop (𝓝 0) ∧
        ∀ (k d : ℕ) (ρ : ℝ), k₀ ≤ k → 2 ≤ k → (k : ℝ) ^ (0.1 : ℝ) ≤ d → 0 < ρ → ρ < 1 →
          ρ ^ 2 * d = 2 * c * Real.log k →
          (∀ π : IdProtocol k d, S ≤ π.success ρ →
            ENNReal.ofReal ((S * (1 - h2 ((1 - c ^ (-(1 / 2 : ℝ))) / 2)) - e k) * (k * d)) ≤
              π.info) ∧
          (∀ (π : IdProtocol k d) (B : ℕ), π.HasWidth B → S ≤ π.success ρ →
            (S * (1 - h2 ((1 - c ^ (-(1 / 2 : ℝ))) / 2)) - e k) * (k * d) ≤ (B : ℝ)) ∧
          ∃ (π : IdProtocol k d) (B : ℕ), π.HasWidth B ∧ S ≤ π.success ρ ∧
            (B : ℝ) ≤ (S * (1 - h2 ((1 - c ^ (-(1 / 2 : ℝ))) / 2)) + e k) * (k * d) ∧
            π.info ≤ ENNReal.ofReal
              ((S * (1 - h2 ((1 - c ^ (-(1 / 2 : ℝ))) / 2)) + e k) * (k * d)) := by sorry

end PreservePast.Supplement
