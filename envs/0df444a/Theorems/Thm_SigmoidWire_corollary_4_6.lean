-- Prove2me | Theorems.Thm_SigmoidWire_corollary_4_6
-- name    : SigmoidWire.corollary_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:07:28.995532+00:00
-- url     : https://prove2.me/theorems/453a1f4a-73f7-47d8-99f5-cf50c9c35ebc
-- title:
--   Corollary 4.6: sign-representation of robust depth-two sigmoidal circuits and the $\Omega(n^2/\log^2 n)$ wire bound
-- statement:
--   1. For every $K$ there is a constant $C$ such that for all $n\ge2$ and every $f:\{0,1\}^n\to\{0,1\}$: every sigmoidal circuit of depth at most $2$ with all weights and biases in $[-n^K,n^K]$ that computes $f$ with separation $n^{-K}$ has a rational sign-representation of $f$ of degree at most $C\sqrt E\log n$, where $E$ is the number of wires of the circuit.
--   2. For every $K$ there is a constant $c>0$ such that for all $n\ge2$, every such circuit computing parity $\oplus_n$ has at least
--
--   $$
--   \frac{c\,n^2}{\log^2 n}
--   $$
--
--   wires.
--
--   **Formalization Note** For $n\ge2$, every polynomial bound on the parameters and every noticeable separation is of the form $n^K$, $n^{-K}$ for a larger $K$.
--
--   Differences from the source:
--   - reading: "polynomial weights and biases", "noticeable separation", O(·), Ω(·) → one K for both: parameters ≤ n^K and separation n^{−K}, constants chosen after K and before n, f and C; reason: for n ≥ 2 every bound a·n^k and b·n^{−k} has this form for a larger K
--   - reading: "depth-two" → depth ≤ 2, measured at the output gate along non-zero weights; reason: the class reading of depth-d circuits; a shallower circuit is not excluded
--   - encoding: bounds in n → n ≥ 2; reason: log 1 = 0 in the denominator; constants absorb small n
--   - reading: "wires (i.e. non-zero parameters)" (p.3) → non-zero weights; biases are not wires; reason: the count "n + n + n" on p.19 counts fan-ins only; a gate with no incoming wire is a constant that folds into its readers' biases, so the two counts agree up to a constant factor
--   - encoding: log, base unspecified → natural logarithm; reason: the base changes only the constant
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Corollary 4.6, p.20

import Mathlib
import Definitions.Def_SigmoidWire_Circuit
import Definitions.Def_SigmoidWire_ComputesSep
import Definitions.Def_SigmoidWire_SignRepBy
import Definitions.Def_GeoQAC_parityFn

namespace SigmoidWire

/-- **Corollary 4.6 (rational sign-representation of robust depth-two sigmoidal circuits, and the
`Ω(n²/log² n)` wire lower bound for parity).**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Corollary 4.6, p.20 (PDF p.22):
"Any function that can be computed by a depth-two sigmoidal circuit containing E wires and using
polynomial weights and biases with noticeable separation, can be sign-represented by a rational
function of degree O(√E log n). Consequently, any depth-two sigmoidal circuit with polynomial weights
and biases that compute Parity with noticeable separation requires Ω(n²/log² n) wires."

**Formalization Note.** "Polynomial weights and biases" and "noticeable separation" are one
exponent `K`: all weights and biases in `[−n^K, n^K]` and separation `n^{−K}`; for `n ≥ 2` every
bound `a·n^k` and every `b·n^{−k}` is of this form for a larger `K`. The constants of `O(·)` and
`Ω(·)` are chosen after `K` and before `n`, the circuit and `f`; `n ≥ 2` (so that `log n > 0`).
`E` is the circuit's own wire count. Depth is measured at the output gate. Parity is the published
`GeoQAC.parityFn n`; `log` is the natural logarithm. -/
theorem corollary_4_6 :
    (∀ K : ℕ, ∃ Cst : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ (f : (Fin n → Bool) → Bool) (C : Circuit n),
      C.depth ≤ 2 → C.ParamsLe ((n : ℝ) ^ K) → ComputesSep Real.sigmoid C f (((n : ℝ) ^ K)⁻¹) →
        SignRepBy f (Cst * Real.sqrt C.wires * Real.log n)) ∧
    (∀ K : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → ∀ C : Circuit n,
      C.depth ≤ 2 → C.ParamsLe ((n : ℝ) ^ K) →
        ComputesSep Real.sigmoid C (GeoQAC.parityFn n) (((n : ℝ) ^ K)⁻¹) →
          c * (n : ℝ) ^ 2 / Real.log n ^ 2 ≤ C.wires) := by sorry

end SigmoidWire
