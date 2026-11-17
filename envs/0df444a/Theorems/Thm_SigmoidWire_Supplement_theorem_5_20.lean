-- Prove2me | Theorems.Thm_SigmoidWire_Supplement_theorem_5_20
-- name    : SigmoidWire.Supplement.theorem_5_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:44:35.69558+00:00
-- url     : https://prove2.me/theorems/4fdf1639-0426-4a60-a3c4-b5ec928997da
-- title:
--   Theorem 5.20 — average sensitivity at most $s^{1-1/d}n^{1-1/(2d)+o(1)}$ for small polynomial-weight depth-$d$ sigmoidal circuits
-- statement:
--   Let $a,d\ge1$ and let $n$ be sufficiently large. Let $C:\{0,1\}^n\to[0,1]$ be a sigmoidal circuit of depth at most $d$ with $s$ gates whose gate-to-gate weights lie in $[-n^a,n^a]$. If $C$ computes a Boolean function $f:\{0,1\}^n\to\{0,1\}$ with separation $\delta\ge n^{-a}$, then
--   $$\mathrm{AS}(f)\ \le\ s^{1-1/d}\cdot n^{1-1/(2d)+o(1)},$$
--   where $\mathrm{AS}(f)=\mathbb E_x\big[\#\{i: f(x)\ne f(x^{(i)})\}\big]$ is the average sensitivity and the $o(1)$ term depends only on $a$ and $d$.
--
--   The bound is the sigmoidal analogue of the average-sensitivity bounds for small threshold circuits.
--
--   Differences from the source:
--   - generalization: weights within [−n^a, n^a] → only the gate-to-gate weights are in [−n^a, n^a] (GateWeightsLe); input weights and biases are arbitrary; reason: the weights of a polynomial-adjusted circuit (Definition 5.27, p.34), the model Lemma 5.28 is proved for; circuits with all weights bounded are a special case
--   - reading: a depth-d sigmoidal circuit with s gates → depth ≤ d (measured at the output), s = C.size + 1 counting every gate; reason: the bound is non-decreasing in d and s
--   - encoding: n^{1−1/(2d)+o(1)} for sufficiently large n → ∀ ε > 0 ∃ N ∀ n ≥ N with exponent 1 − 1/(2d) + ε; reason: the o(1) depends on a and d only
--   - encoding: separation δ ≥ n^{−a} → ComputesSep with separation n^{−a}; reason: every larger separation implies it
--   - encoding: AS(f) (Definition 3.8) → the published GeoQAC.avgSens f; reason: the same quantity: the uniform average of the number of sensitive coordinates
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 5.20, p.32 (restated p.37)

import Mathlib
import Definitions.Def_SigmoidWire_Circuit
import Definitions.Def_SigmoidWire_ComputesSep
import Definitions.Def_GeoQAC_avgSens
import Definitions.Def_SigmoidWire_Supplement_GateWeightsLe

namespace SigmoidWire.Supplement

open SigmoidWire

/-- **Theorem 5.20 (average sensitivity of functions computed by small polynomial-weight
sigmoidal circuits).**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 5.20, p.32 (PDF p.34), restated p.37 (PDF p.39): "For any a, d ≥ 1 and sufficiently
large n, let C : {0,1}^n → [0,1] be any depth-d sigmoidal circuit with s gates and weights within
[−n^a, n^a]. Suppose that it computes a Boolean function f : {0,1}^n → {0,1} with separation
δ ≥ n^{−a}, then AS(f) ≤ s^{1−1/d} · n^{1−1/(2d)+o(1)}."

**Formalization Note.** The `o(1)` depends on `a, d` only: "for every `ε > 0` there is `N`".
`s = C.size + 1`; depth at most `d`; only gate-to-gate weights are bounded (`GateWeightsLe`,
Definition 5.27); separation `δ ≥ n^{−a}` is `ComputesSep … (n^{−a})`. `AS(f)` is the published
`GeoQAC.avgSens f`, the uniform average over `x` of the number of coordinates `i` with
`f(x) ≠ f(x^{(i)})` (Definition 3.8, p.16). -/
theorem theorem_5_20 :
    ∀ a : ℝ, 1 ≤ a → ∀ d : ℕ, 1 ≤ d → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ C : Circuit n, C.depth ≤ d → GateWeightsLe C ((n : ℝ) ^ a) →
      ∀ f : (Fin n → Bool) → Bool, ComputesSep Real.sigmoid C f ((n : ℝ) ^ (-a)) →
        GeoQAC.avgSens f ≤ ((C.size + 1 : ℕ) : ℝ) ^ (1 - 1 / (d : ℝ)) *
          (n : ℝ) ^ (1 - 1 / (2 * (d : ℝ)) + ε) := by sorry

end SigmoidWire.Supplement
