-- Prove2me | Theorems.Thm_SigmoidWire_theorem_4_1
-- name    : SigmoidWire.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:07:15.579583+00:00
-- url     : https://prove2.me/theorems/38f2f3ac-dfdd-4125-9d25-c1fdda33c36b
-- title:
--   Theorem 4.1: symmetric functions by depth-three sigmoidal circuits with $O(n)$ wires
-- statement:
--   There are constants $C,K,\varepsilon_0>0$ such that for every $n\ge1$ and every symmetric Boolean function $f:\{0,1\}^n\to\{0,1\}$ there is a sigmoidal circuit of depth at most $3$ with at most $Cn$ wires, all of whose weights and biases have absolute value at most $Cn^K$, computing $f$ with separation $\varepsilon_0$.
--
--   This is the upper-bound half of the mission's headline for depth three. Threshold circuits of any constant depth need super-linearly many wires for parity, so the theorem shows an advantage of real-valued gates.
--
--   Differences from the source:
--   - generalization: "polynomial weights" → every weight and every bias is at most Cc·n^K in absolute value; reason: the proof bounds both (p.19), and a bound on biases too implies the stated bound on weights
--   - reading: "depth-three" → depth ≤ 3, measured at the output gate along non-zero weights; reason: the class reading of depth-d circuits; a shallower circuit is not excluded
--   - encoding: O(n)-type bounds "for large n" → constants Cc, K, ε₀ chosen before n and f, for all n ≥ 1; reason: small n are absorbed by the constants; this is not a narrowing
--   - reading: "wires (i.e. non-zero parameters)" (p.3) → non-zero weights; biases are not wires; reason: the count "n + n + n" on p.19 counts fan-ins only; a gate with no incoming wire is a constant that folds into its readers' biases, so the two counts agree up to a constant factor
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 4.1, p.18

import Mathlib
import Definitions.Def_ShallowSym_IsSymmetric
import Definitions.Def_SigmoidWire_Circuit
import Definitions.Def_SigmoidWire_ComputesSep

namespace SigmoidWire

/-- **Theorem 4.1 (symmetric functions by depth-three sigmoidal circuits with `O(n)` wires).**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 4.1, p.18 (PDF p.20):
"For every symmetric Boolean function f : {0, 1}^n → {0, 1}, there is a depth-three sigmoidal circuit
with O(n) wires and polynomial weights that computes f with separation Ω(1)."

**Formalization Note.** The constants `Cc`, `K`, `ε₀` are chosen before `n` and `f`: wires
`≤ Cc · n`, every weight **and bias** of absolute value `≤ Cc · n^K` (the proof bounds both, p.19),
separation `ε₀ > 0`. "Depth-three" is `depth ≤ 3`, measured at the output gate. `n ≥ 1`. -/
theorem theorem_4_1 :
    ∃ Cc : ℝ, ∃ K : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ n : ℕ, 1 ≤ n → ∀ f : (Fin n → Bool) → Bool, ShallowSym.IsSymmetric f →
        ∃ C : Circuit n, C.depth ≤ 3 ∧ (C.wires : ℝ) ≤ Cc * n ∧
          C.ParamsLe (Cc * (n : ℝ) ^ K) ∧ ComputesSep Real.sigmoid C f ε₀ := by sorry

end SigmoidWire
