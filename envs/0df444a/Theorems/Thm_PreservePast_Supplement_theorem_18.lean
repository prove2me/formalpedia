-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_18
-- name    : PreservePast.Supplement.theorem_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:42:13.428873+00:00
-- url     : https://prove2.me/theorems/69878152-1489-48a6-82de-b1ba61485dfa
-- title:
--   Theorem 18 — fixed-channel retention frontier
-- statement:
--   In the nearest-of-$k$ experiment on the cube, fix $0<\rho<1$ and $0<R<1-h_2((1-\rho)/2)$. Let $d\to\infty$ with $\log_2k/d\to R$, and define
--   $$b^\ast=\frac{1-2h_2^{-1}(1-R)}{\rho},\qquad r_{R,\rho}=1-h_2\Big(\frac{1-b^\ast}2\Big).$$
--   Every joint randomized protocol satisfies $I(X;M\mid R)/(kd)\ge S\,r_{R,\rho}-o(1)$. For fixed $0<S<1$,
--   $$C(S)/(kd)=S\,r_{R,\rho}+o(1),\qquad C\in\{I_{\min},B_{\min}\}.$$
--   A finite-width sequence with success tending to one and normalized cost tending to $r_{R,\rho}$ exists.
--
--   This is the identification–storage frontier at a fixed channel, for arbitrary joint randomized messages.
--
--   **Formalization Note** The regime is an arbitrary sequence $(k_n,d_n)$ with $k_n\ge2$, $d_n\to\infty$ and $\log_2k_n/d_n\to R$. In $I(X;M\mid R)$ the letter $R$ denotes the public coins.
--
--   Differences from the source:
--   - encoding: o(1) as k → ∞ (resp. d → ∞), for every sequence of protocols → a sequence e → 0 valid for all admissible parameters and all protocols at each index; reason: equivalent to the statement for every sequence of parameters and protocols
--   - encoding: C(S)/(kd) = S·r + o(1) for C ∈ {I_min, B_min} → every protocol of success ≥ S has information and width ≥ (S·r − e)kd, and from some index on a protocol of success ≥ S has width and information ≤ (S·r + e)kd; reason: two-part form of a least cost; avoids junk values of infima
--   - reading: h₂⁻¹(1 − R) → the inverse of h₂ on the branch [0, 1/2]; reason: on this branch 0 < b* < 1 under the hypothesis R < 1 − h₂((1−ρ)/2); the other branch gives b* < 0
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 18, p.63 (PDF p.65), eq. (229); Definition 1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_PreservePast_Supplement_IdProtocol

open MeasureTheory Filter Topology

namespace PreservePast.Supplement

/-- **Theorem 18 (Fixed-channel retention frontier).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Theorem 18, p.63 (PDF p.65),
eq. (229); the experiment is Definition 1, p.10 (PDF p.12).

Fix `0 < ρ < 1` and `0 < R < 1 − h₂((1−ρ)/2)`. Let `d → ∞` with `log₂ k/d → R`, and
`b* = [1 − 2h₂⁻¹(1 − R)]/ρ`, `r_{R,ρ} = 1 − h₂((1 − b*)/2)`. Every protocol has
`I(X; M | R)/(kd) ≥ S r_{R,ρ} − o(1)`; for fixed `0 < S < 1`,
`C(S)/(kd) = S r_{R,ρ} + o(1)` for `C ∈ {I_min, B_min}`; and a finite-width sequence with success
tending to one and normalized cost tending to `r_{R,ρ}` exists.

**Formalization Note.** The regime is an arbitrary sequence `(k_n, d_n)` with `k_n ≥ 2`,
`d_n → ∞` and `log₂ k_n/d_n → R` (the rate is the binder `Rt`; the letter `R` of
`I(X; M | R)` is the public coins). `h₂⁻¹` is the inverse on the branch `[0, 1/2]` (`h2inv`),
for which `0 < b* < 1`. Each `o(1)` is a sequence `e_n → 0` valid for all protocols at index
`n`. (229) is stated in two parts for each cost as in Theorem 17; the existence clauses hold
from some index on. The last clause gives a width `B ≤ (r_{R,ρ} + e_n)kd`; with the first
clause its normalized cost tends to `r_{R,ρ}`. -/
theorem theorem_18 :
    ∀ ρ Rt : ℝ, 0 < ρ → ρ < 1 → 0 < Rt → Rt < 1 - h2 ((1 - ρ) / 2) →
      ∀ k d : ℕ → ℕ, (∀ n, 2 ≤ k n) → Tendsto d atTop atTop →
        Tendsto (fun n => Real.logb 2 (k n) / d n) atTop (𝓝 Rt) →
        (∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ n,
          (∀ π : IdProtocol (k n) (d n),
            ENNReal.ofReal ((π.success ρ * (1 - h2 ((1 - (1 - 2 * h2inv (1 - Rt)) / ρ) / 2)) -
              e n) * (k n * d n)) ≤ π.info) ∧
          ∃ (π : IdProtocol (k n) (d n)) (B : ℕ), π.HasWidth B ∧ 1 - e n ≤ π.success ρ ∧
            (B : ℝ) ≤ ((1 - h2 ((1 - (1 - 2 * h2inv (1 - Rt)) / ρ) / 2)) + e n) *
              (k n * d n)) ∧
        ∀ S : ℝ, 0 < S → S < 1 → ∃ (e : ℕ → ℝ) (n₀ : ℕ), Tendsto e atTop (𝓝 0) ∧ ∀ n, n₀ ≤ n →
          (∀ π : IdProtocol (k n) (d n), S ≤ π.success ρ →
            ENNReal.ofReal ((S * (1 - h2 ((1 - (1 - 2 * h2inv (1 - Rt)) / ρ) / 2)) - e n) *
              (k n * d n)) ≤ π.info) ∧
          (∀ (π : IdProtocol (k n) (d n)) (B : ℕ), π.HasWidth B → S ≤ π.success ρ →
            (S * (1 - h2 ((1 - (1 - 2 * h2inv (1 - Rt)) / ρ) / 2)) - e n) * (k n * d n) ≤
              (B : ℝ)) ∧
          ∃ (π : IdProtocol (k n) (d n)) (B : ℕ), π.HasWidth B ∧ S ≤ π.success ρ ∧
            (B : ℝ) ≤ (S * (1 - h2 ((1 - (1 - 2 * h2inv (1 - Rt)) / ρ) / 2)) + e n) *
              (k n * d n) ∧
            π.info ≤ ENNReal.ofReal
              ((S * (1 - h2 ((1 - (1 - 2 * h2inv (1 - Rt)) / ρ) / 2)) + e n) *
                (k n * d n)) := by sorry

end PreservePast.Supplement
