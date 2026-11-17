-- Prove2me | Theorems.Thm_SigmoidWire_Supplement_theorem_1_7
-- name    : SigmoidWire.Supplement.theorem_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:46:33.293019+00:00
-- url     : https://prove2.me/theorems/91230366-40ea-491b-9872-f754dbdddd86
-- title:
--   Theorem 1.7 — $\mathrm{IP2}$ by an unrestricted-weight sigmoidal circuit with $O(\sqrt n\log n)$ gates
-- statement:
--   There are absolute constants $C$ and $\varepsilon_0>0$ such that for every $n\ge2$ the inner product mod 2 on $2n$ bits,
--   $$\mathrm{IP2}(x,y)=\sum_{i=1}^nx_iy_i\bmod 2,$$
--   is computed with separation $\varepsilon_0$ by a sigmoidal circuit (unrestricted weights, biases and depth) with at most
--   $$C\sqrt n\,\log n$$
--   gates.
--
--   Threshold circuits need $\Omega(n)$ gates and ReLU circuits $\Omega(n/\log n)$ gates for $\mathrm{IP2}$, so this separates sigmoidal circuits from both.
--
--   Differences from the source:
--   - generalization: "can be computed" by an unrestricted-weight sigmoidal circuit, i.e. with no separation (p.3) → computed with one constant separation ε₀ > 0 (ComputesSep … ε₀); reason: the construction makes the output gate within 1/8 of the bit (p.45); separation ε₀ implies no separation, so the Lean specializes to the source
--   - encoding: O(√n log n) gates → ∃ C: at most C·√n·log n gates (C.size + 1, all gates) for every n ≥ 2, natural log; reason: the base changes only C; √n log n = 0 at n = 1
--   - encoding: x, y ∈ {0,1}^n, 2n inputs → Circuit (n + n), x the first n inputs; reason: Lean indexing
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 1.7, p.5; restated with its proof in §6.3, pp.42–45

import Mathlib
import Definitions.Def_SigmoidWire_Circuit
import Definitions.Def_SigmoidWire_ComputesSep
import Definitions.Def_SigmoidWire_Supplement_ip2

namespace SigmoidWire.Supplement

open SigmoidWire

/-- **Theorem 1.7 (IP2 with `O(√n log n)` sigmoidal gates).**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 1.7, p.5 (PDF p.7), restated with its proof in §6.3, p.42 (PDF p.44):
"Theorem 1.7 (see Section 6.3). IP2 can be computed by an unrestricted-weight sigmoidal circuit with
O(√n log n) gates."

**Formalization Note.** `n` is the length of each of `x` and `y` (2n input bits). There are absolute
constants `Cc` and `ε₀ > 0` such that for every `n ≥ 2` some circuit with at most `Cc·√n·log n`
gates (`C.size + 1`, all gates counted) computes IP2 with separation `ε₀`. "Computed" is read as
computing with a constant separation, which the construction gives (its output is within `1/8` of
the bit, p.45) and which implies computing with no separation. Weights, biases and depth are
unrestricted; `log` is the natural logarithm (the base only changes `Cc`); `n ≥ 2` because
`√n·log n = 0` at `n = 1`. -/
theorem theorem_1_7 :
    ∃ Cc ε₀ : ℝ, 0 < ε₀ ∧ ∀ n : ℕ, 2 ≤ n → ∃ C : Circuit (n + n),
      ((C.size + 1 : ℕ) : ℝ) ≤ Cc * Real.sqrt n * Real.log n ∧
        ComputesSep Real.sigmoid C (ip2 n) ε₀ := by sorry

end SigmoidWire.Supplement
