-- Prove2me | Theorems.Thm_PrivRobustStat_lemma_17
-- name    : PrivRobustStat.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:51:27.735189+00:00
-- url     : https://prove2.me/theorems/cbc7414d-3b44-464d-bf58-27a03882a4da
-- title:
--   Lemma 17, p.37 (corrected: $\log d$ read as $\max\{1,\log d\}$) — Algorithm 8 after localization is $(\lambda,\rho)$-RDP with $\rho$ as in (45)
-- statement:
--   **Lemma 17.** For every value $C_r>0$ of the sketch constant there is $C>0$ such that the following holds. Let $d\ge1$, a public centre $q$ (the output of localization), $R_0>0$, $\kappa_\star\in(0,R_0^2)$, $\alpha,\beta\in(0,\tfrac14)$, let $T$ and $\kappa_T$ be as in Algorithm 8, and $L=\max\{1,\log d\}$. Then the output $c_T$ of Algorithm 8 (after Line 1) is $(\lambda,\rho)$-RDP for every $\lambda>1$, over all neighbouring datasets, with
--
--   $$\rho=\frac C{n^2}\Big(\frac{(T+1)dR_0^2L^5}{\alpha\kappa_T}\log\frac{(n+d)(T+1)}\beta+\frac{(T+1)^3L^2}{\alpha^2}\log\frac{(T+1)^2L}{\alpha\beta}+\frac{R_0^2(d+\log\frac{T+1}\beta)}{\kappa_T}\Big(\frac1\alpha+L^2\Big)\Big).\tag{45}$$
--
--   Converting this RDP bound to $(\varepsilon/2,\delta/2)$-DP gives the privacy part of Theorem 4.
--
--   Differences from the source:
--   - correction: log(d), log⁵(d), log²(d) in (45) → max{1, log d} in each place; reason: at d = 1 the printed (45) has no filtering term (log 1 = 0), but every filtering call releases Gaussian sketches whose sensitivity is positive for some neighbours, with RDP cost growing with the sketch dimension r ∝ log((n + 1)/β₀); a bound C/n²·(R₀²(1 + log((T+1)/β))/κ_T·(1/α)) independent of log n then fails for large n; for d ≥ 3 nothing changes
--   - encoding: "For any fixed q, the output c_T of Algorithm 8" → Algorithm 8 after Line 1 with the localized centre public; RDP over every pair of neighbouring datasets in (ℝ^d)^n; reason: "for any fixed q" fixes the output of Line 1
--   - reading: ρ ≤ (45) → (λ, ρ)-RDP with ρ equal to the right side of (45); reason: RDP is monotone in ρ
--   - generalization: α ∈ (0, α⋆) (Algorithm 8's input) → α ∈ (0, 1/4) (Algorithm 1's input range); reason: α⋆ ≤ 1/4, so the source's range is included
--   - generalization: r with the universal constant of Lemma 6 → any sketch constant C_r > 0, with C depending on C_r; reason: the paper's case is C_r = the constant of Lemma 6
--   - encoding: "for a sufficiently large constant C > 0" → ∃ C > 0 after C_r and before every other quantity; reason: meaning of the constant
--   - encoding: the output law of the mechanism → the law is the pushforward of the noise measure, and the item also asserts the output map is measurable; reason: Lean pushes a non-measurable map to the zero measure, under which privacy would hold vacuously; measurability rules this out and changes no instance
--   - encoding: the running time of Lemma 17 → not in this item; the mission goal theorem_4 bounds the work of a machine program; reason: the item states the algorithm as a random map of data and noise, which has no cost (planning decision 10)
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Lemma 17, p.37 (PDF p.40); proof pp.37–38; Algorithm 8, p.34

import Mathlib
import Definitions.Def_PrivRobustStat_MeanEst

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat

/-- **Lemma 17** (privacy accounting of Algorithm 8), p.37 (PDF p.40); proof pp.37–38.

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…).

"For any fixed q, the output c_T of Algorithm 8 satisfies (λ, ρ)-RDP for every λ > 1, where
ρ ≤ C/n² ( (T+1)dR₀² log⁵(d)/(ακ_T) · log((n+d)(T+1)/β) + (T+1)³ log²(d)/α² · log((T+1)² log(d)/(αβ))
+ R₀²(d + log((T+1)/β))/κ_T · (1/α + log²(d)) ) (45) for a sufficiently large constant C > 0. The
algorithm runs in time O(nd(T+1) log²(d) log((n+d)(T+1)/β) + nT log((T+1) log(d)/α))."

**Formalization Note.**
* "For any fixed q": the mechanism is Algorithm 8 after Line 1 (`alg8`), with the localized centre
  `qc` public. Public inputs: `R₀ > 0`, `κ⋆ ∈ (0, R₀²)`, `α, β ∈ (0, 1/4)`, `d ≥ 1`; `T = roundsT`,
  `κ_T = kappaT d R₀ T`. RDP is over every pair of neighbouring datasets in `(ℝ^d)^n`; the output is
  a measurable function of the draws.
* Correction: every `log(d)` is read as `max{1, log d}`; at `d = 1` the printed (45) drops the
  filtering calls' sketch cost, which grows with `log n`.
* Algorithm 8's input `α ∈ (0, α⋆)` is widened to `α ∈ (0, 1/4)` (Algorithm 1's range).
* The sketch-dimension constant `Cr` is any positive number; `C` may depend on it. The running time
  is carried by the goal theorem's time clause. -/
theorem lemma_17 :
    ∀ Cr : ℝ, 0 < Cr → ∃ C : ℝ, 0 < C ∧
      ∀ {d n : ℕ}, 1 ≤ d → ∀ (qc : Vec d) (R0 κstar α β : ℝ),
        0 < R0 → 0 < κstar → κstar < R0 ^ 2 → 0 < α → α < 1 / 4 → 0 < β → β < 1 / 4 →
        (∀ x : Fin n → Vec d, Measurable fun g : A8Idx d (r8 Cr n d R0 κstar β) → ℝ =>
          alg8 Cr x qc R0 κstar α β g) ∧
        ∀ lam : ℝ, 1 < lam →
          IsRDPOn (fun _ : Fin n → Vec d => True) lam
            (C / (n : ℝ) ^ 2 *
              (((roundsT d R0 κstar : ℝ) + 1) * d * R0 ^ 2 * max 1 (Real.log d) ^ 5 /
                    (α * kappaT d R0 (roundsT d R0 κstar)) *
                  Real.log ((((n : ℝ) + d) * ((roundsT d R0 κstar : ℝ) + 1)) / β) +
                ((roundsT d R0 κstar : ℝ) + 1) ^ 3 * max 1 (Real.log d) ^ 2 / α ^ 2 *
                  Real.log (((roundsT d R0 κstar : ℝ) + 1) ^ 2 * max 1 (Real.log d) / (α * β)) +
                R0 ^ 2 * ((d : ℝ) + Real.log (((roundsT d R0 κstar : ℝ) + 1) / β)) /
                    kappaT d R0 (roundsT d R0 κstar) *
                  (1 / α + max 1 (Real.log d) ^ 2)))
            (fun x => (stdGauss (A8Idx d (r8 Cr n d R0 κstar β))).map fun g =>
              alg8 Cr x qc R0 κstar α β g) := by sorry

end PrivRobustStat
