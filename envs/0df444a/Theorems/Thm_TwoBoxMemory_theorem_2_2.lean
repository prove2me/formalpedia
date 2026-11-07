-- Prove2me | Theorems.Thm_TwoBoxMemory_theorem_2_2
-- name    : TwoBoxMemory.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:52.925443+00:00
-- url     : https://prove2.me/theorems/51818725-8f40-453c-964c-885acd1b1bc1
-- title:
--   Theorem 2.2 — arithmetic memory bounds and a rational instance
-- statement:
--   Let $\Delta_M=V_M-V$ be the excess of the best controller with at most $M$ labels over the unrestricted value, where $V_M$ ranges over all real stochastic controllers with arbitrary initial distributions.
--
--   1. **Gap-sensitive bounds.** For every non-tie positive saddle $(r,s,\beta,D)$ with irrational logarithmic failure ratio, with saddle cost $C=Dv/u$ and greedy word $W$, and every $M\ge2$,
--   $$\tfrac12\,d_{F_M}\ \le\ \Delta_M\ \le\ K_0'M\tau^{H_M},\qquad F_M\le2H_M,\qquad 0<\tau<1 .$$
--   2. **Matching exponential order.** If moreover $|\beta r^i-s^j|\ge a e^{-c(i+j)}$ for all $i,j\ge0$ with some $a,c>0$, then $-\log\Delta_M=\Theta(H_M)$ as $M\to\infty$: there are $c_1,c_2>0$ and $M_0$, depending on the instance, with $c_1H_M\le-\log\Delta_M\le c_2H_M$ for all $M\ge M_0$.
--   3. **When separation holds.** The separation hypothesis holds for rational non-tie $(r,s,\beta)$ (with $r,s\in(0,1)$, $\beta>0$), and, for fixed $r,s\in(0,1)$ with $\log r/\log s$ irrational, for Lebesgue-almost every $\beta>0$.
--   4. **A rational instance.** For $r=1/7$, $s=2/3$, $D=1$ and the dyadic cost $C_0=254613987398388214970098320848945712466442749572012796843191368/2^{200}$,
--   $$\Delta_{28}(C_0)\ge2^{-31},\qquad \Delta_{29}(C_0)\le2^{-179},\qquad \Delta_{29}(C_0)\le2^{-148}\,\Delta_{28}(C_0) .$$
--
--   The theorem says that the memory needed for near-optimal two-location search is governed by the repetition horizon $H_M$ of the optimal word, and that one additional label can reduce the excess by a factor of $2^{148}$ at an explicit rational input.
--
--   **Formalization Note** $\Theta$ is read as in Theorem B.4 (p.24), with constants depending on the fixed instance and not on $M$.
--
--   Differences from the source:
--   - reading: −log Δ_M = Θ(H_M) → ∃ c₁ > 0, ∃ c₂ > 0, ∃ M₀, ∀ M ≥ M₀, c₁ H_M ≤ −log Δ_M ≤ c₂ H_M; reason: Theorem B.4 (p.24) states it 'as M → ∞, with constants depending on the fixed search instance'
--   - generalization: separation holds for rational non-tie (r, s, β) at a non-tie positive saddle with irrational logarithmic failure ratio → separation holds for every rational r, s ∈ (0, 1), β > 0 with no tie; reason: the proof (B.15) uses only rationality and non-tie; adding the saddle hypotheses gives the source's claim
--   - generalization: for almost every index β (satisfying u, v > 0, Theorem B.4 (ii)) at any fixed irrational logarithmic failure ratio → for Lebesgue almost every β > 0; reason: the proof works on the whole positive axis (p.24); restricting to u, v > 0 gives the source's claim
--   - encoding: $\Delta_M=V_M-V$ with $V_M,V\in[0,\infty]$ → `gap` $=(V_M).\mathrm{toReal}-V.\mathrm{toReal}$; reason: both values are finite for $M\ge1$ (proved in the verification file), so the real difference is exact
--   - encoding: controller risk as the risk (B.4) of the cylinder law $\mu K_{x_0}\cdots K_{x_{h-1}}\mathbf 1$ (p.2) → closed form $\sum_{n\ge0}\mu Q_h^n c$ of Appendix C, p.28; reason: the paper states both forms of the same quantity; every term is nonnegative
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), Theorem 2.2, p.3 (PDF 5); proofs in §§6–8, pp.8–11 (PDF 10–13) and Appendix B, pp.20–27 (PDF 22–29)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Saddle
import Definitions.Def_TwoBoxMemory_Profile
import Definitions.Def_TwoBoxMemory_Constants
import Definitions.Def_TwoBoxMemory_Instance
open MeasureTheory

namespace TwoBoxMemory

/-- Theorem 2.2 (Arithmetic memory bounds and a rational instance).
(a) For a non-tie positive saddle `(r, s, β, D)` with irrational logarithmic failure ratio and its
    saddle cost `C = D v / u`, for every `M ≥ 2`: `½ d_{F_M} ≤ Δ_M ≤ K′₀ M τ^{H_M}`,
    `F_M ≤ 2 H_M`, `0 < τ < 1`. The lower bound includes all real randomized controllers.
(b) If moreover `|β r^i − s^j| ≥ a e^{−c(i+j)}` for all `i, j ≥ 0` (some `a, c > 0`), then
    `−log Δ_M = Θ(H_M)` as `M → ∞`, with constants depending on the instance.
(c) The separation hypothesis holds for rational non-tie `(r, s, β)`, and, at any fixed irrational
    logarithmic failure ratio, for Lebesgue-almost every index `β`.
(d) For the rational physical cost `C₀` of Section 8, with `r = 1/7`, `s = 2/3`, `D = 1`:
    `Δ₂₈(C₀) ≥ 2^{−31}`, `Δ₂₉(C₀) ≤ 2^{−179}`, `Δ₂₉(C₀) ≤ 2^{−148} Δ₂₈(C₀)`.

**Formalization Note.** `Θ` is read as in Theorem B.4 (p.24): there are `c₁, c₂ > 0` and `M₀`,
depending on the instance, with `c₁ H_M ≤ −log Δ_M ≤ c₂ H_M` for all `M ≥ M₀`. Clause (c) is
stated for rationals `r, s ∈ (0, 1)`, `β > 0` with no tie, and for almost every `β > 0`.

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
Theorem 2.2, p.3 (PDF 5); proofs §§6–8, pp.8–11 (PDF 10–13) and Appendix B, pp.20–27 (PDF 22–29).

Standing setting: commands are `Fin 2` with `0 = A`, `1 = B`; risks are in `ℝ≥0∞`; `gap` is
`Δ_M = V_M − V` as a real number. -/
theorem theorem_2_2 :
    (∀ r s β D : ℝ, IsSaddle r s β D → ∀ M : ℕ, 2 ≤ M →
      departureMargin r s β D (profF (greedyWord r s β) M) / 2 ≤ gap r s (saddleCost r s β D) D M ∧
      gap r s (saddleCost r s β D) D M ≤ K0' r s β (saddleCost r s β D) D * M * tau r s ^ profH (greedyWord r s β) M ∧
      profF (greedyWord r s β) M ≤ 2 * profH (greedyWord r s β) M ∧ 0 < tau r s ∧ tau r s < 1) ∧
    (∀ r s β D : ℝ, IsSaddle r s β D → Sep r s β →
      ∃ c₁ > 0, ∃ c₂ > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀,
        c₁ * profH (greedyWord r s β) M ≤ -Real.log (gap r s (saddleCost r s β D) D M) ∧
        -Real.log (gap r s (saddleCost r s β D) D M) ≤ c₂ * profH (greedyWord r s β) M) ∧
    (∀ r s β : ℚ, 0 < r → r < 1 → 0 < s → s < 1 → 0 < β → IsNonTie r s β → Sep r s β) ∧
    (∀ r s : ℝ, 0 < r → r < 1 → 0 < s → s < 1 → Irrational (Real.log r / Real.log s) →
      ∀ᵐ β ∂(volume : Measure ℝ), 0 < β → Sep r s β) ∧
    ((2 : ℝ) ^ (-31 : ℤ) ≤ gap (1 / 7) (2 / 3) C0 1 28 ∧
      gap (1 / 7) (2 / 3) C0 1 29 ≤ (2 : ℝ) ^ (-179 : ℤ) ∧
      gap (1 / 7) (2 / 3) C0 1 29 ≤ (2 : ℝ) ^ (-148 : ℤ) * gap (1 / 7) (2 / 3) C0 1 28) := by sorry

end TwoBoxMemory
