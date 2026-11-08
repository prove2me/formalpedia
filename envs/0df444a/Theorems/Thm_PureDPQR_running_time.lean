-- Prove2me | Theorems.Thm_PureDPQR_running_time
-- name    : PureDPQR.running_time
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:00:58.441212+00:00
-- url     : https://prove2.me/theorems/d584199f-bafe-4034-bea9-3b393af9af57
-- title:
--   Proof of Theorem 2 (§6.3), p.28 — Algorithm 2 runs in $O(dkT)$ operations in the model of Remark 24
-- statement:
--   **Running time of Algorithm 2** (proof of Theorem 2, §6.3). In the computational model of Remark 24 there is a constant $c$ and a single program that, on every instance with $N\ge1$, $d\ge2$, $k\ge1$, $0<\varepsilon\le1$, $0<\beta<\frac12$, a query table in $[0,1]^{k\times d}$ and $h\in H_{N,d}$, outputs a sample of Algorithm 2's output law and halts within
--
--   $$c\,d\,k\,T\qquad\text{steps},\qquad T=\lceil N\varepsilon/\log(2k)\rceil .$$
--
--   Since $T\le N/\log2+1$, this gives the polynomial running time of Theorem 2.
--
--   **Formalization Note** The model is the randomized exact real RAM `PureDPQR.Machine`. One admissible program $P$ and one $c$ are chosen before all parameters; the law of $P$'s output on the standard input layout equals `alg2Law h`, and $P$ halts within $c\,d\,k\,T$ steps on every tape.
--
--   Differences from the source:
--   - reading: "the total is O(dkT)" in the model of Remark 24 → ∃ c, ∃ admissible program P: programLaw P (goalInput …) = alg2Law h and P halts within c·d·k·T steps on every tape; reason: Remark 24 fixes the cost model; one program for all instances makes O(·) uniform; the law equality ties P to Algorithm 2
--   - reading: unit-cost Laplace and Bernoulli sampling (Remark 24) → no such instructions; draws are computed from Uniform(0,1) tape cells; reason: a weaker machine makes the statement stronger; the inverse-CDF formulas cost O(1)
--   - encoding: Algorithm 2, a randomized procedure → its output law alg2Law = Σ_y Q_h(y) δ_{D(y)}, with Q_h(y) the integral smoothed; reason: Z_j = B_j L_j has law (1−π)δ₀ + πLap(κ) and y given Z has law p_{h+Z}, so this is the law of the output
--   - encoding: Lap(κ) of rate κ → PrivLearn.Generic.laplace κ⁻¹ (scale parameter); reason: the published Laplace law is parametrized by its scale; same law
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), Proof of Theorem 2 (§6.3), p.28 (PDF p.29); Remark 24, p.28

import Mathlib
import Definitions.Def_PureDPQR_IsDP
import Definitions.Def_PureDPQR_alg2Law
import Definitions.Def_PureDPQR_Machine

namespace PureDPQR

/-- **Running time of Algorithm 2**, proof of Theorem 2 (§6.3), p.28 (PDF p.29), in the model of
Remark 24, p.28.

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…).

"For the running time, we count operations in the model of Remark 24. Forming the signed query list
takes O(dk) operations. The independent Bernoulli and Laplace draws take O(d) operations under our
unit-cost sampling assumptions. In each of the T rounds, computing all K = 2k inner products costs
O(dk) operations. Evaluating the softmax weights and sampling from their cumulative probabilities
costs O(k), and updating the weights costs O(d). The decoder can accumulate the average of the
iterates in O(d) operations per round. Since T = ⌈Nε/ log(2k)⌉ ≥ 1, the total is O(dkT)."

**Formalization Note.**
* The model of Remark 24 is the machine `PureDPQR.Machine` (exact real arithmetic and comparisons,
  `exp`, `log`, `sqrt`, independent Uniform(0,1) draws, unit cost per instruction; Laplace and
  Bernoulli draws are computed from uniforms at constant cost). One admissible program `P` and one
  constant `c` are chosen before all parameters.
* "Algorithm 2 runs in O(dkT)" is read as: on the input layout `goalInput` of every instance in the
  ranges of Theorem 2, the law of `P`'s output equals Algorithm 2's output law `alg2Law`, and `P`
  halts within `c·d·k·T` steps on **every** tape, `T = ⌈Nε/log(2k)⌉` (`TParam`). -/
theorem running_time :
    ∃ c : ℕ, ∃ P : Program, Admissible P ∧
      ∀ (N d k : ℕ) (ε β : ℝ), 1 ≤ N → 2 ≤ d → 1 ≤ k → 0 < ε → ε ≤ 1 → 0 < β → β < 1 / 2 →
        ∀ Q : Fin k → Fin d → ℝ, (∀ i j, Q i j ∈ Set.Icc (0 : ℝ) 1) →
          ∀ h ∈ histograms N d,
            programLaw P d (goalInput N d k ε β Q h) = alg2Law N d k ε β Q h ∧
              ∀ ω : ℕ → ℝ,
                HaltsWithin P (goalInput N d k ε β Q h) (c * d * k * TParam N k ε) ω := by sorry

end PureDPQR
