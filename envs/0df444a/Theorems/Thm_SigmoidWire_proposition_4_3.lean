-- Prove2me | Theorems.Thm_SigmoidWire_proposition_4_3
-- name    : SigmoidWire.proposition_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:07:33.261309+00:00
-- url     : https://prove2.me/theorems/4eb14bac-100b-4646-bbd3-1ea28f3f333f
-- title:
--   Proposition 4.3: symmetric functions by depth-two sigmoidal circuits with $O(n^2)$ wires
-- statement:
--   There are constants $C,K,\varepsilon_0>0$ such that for every $n\ge1$ and every symmetric Boolean function $f:\{0,1\}^n\to\{0,1\}$ there is a sigmoidal circuit of depth at most $2$ with at most $Cn^2$ wires, all of whose weights and biases have absolute value at most $Cn^K$, computing $f$ with separation $\varepsilon_0$.
--
--   By the lower bound of Corollary 4.6, this is tight for parity up to the factor $\log^2 n$.
--
--   Differences from the source:
--   - generalization: "polynomial weights" → every weight and every bias is at most Cc·n^K in absolute value; reason: the proof bounds both (p.19), and a bound on biases too implies the stated bound on weights
--   - reading: "depth-two" → depth ≤ 2, measured at the output gate along non-zero weights; reason: the class reading of depth-d circuits; a shallower circuit is not excluded
--   - encoding: O(n)-type bounds "for large n" → constants Cc, K, ε₀ chosen before n and f, for all n ≥ 1; reason: small n are absorbed by the constants; this is not a narrowing
--   - reading: "wires (i.e. non-zero parameters)" (p.3) → non-zero weights; biases are not wires; reason: the count "n + n + n" on p.19 counts fan-ins only; a gate with no incoming wire is a constant that folds into its readers' biases, so the two counts agree up to a constant factor
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Proposition 4.3, p.19

import Mathlib
import Definitions.Def_ShallowSym_IsSymmetric
import Definitions.Def_SigmoidWire_Circuit
import Definitions.Def_SigmoidWire_ComputesSep

namespace SigmoidWire

/-- **Proposition 4.3 (symmetric functions by depth-two sigmoidal circuits with `O(n²)` wires).**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Proposition 4.3, p.19
(PDF p.21): "For every symmetric function f : {0, 1}^n → {0, 1}, there is a depth-two
polynomial-weight sigmoidal circuit with O(n²) wires that computes f with separation Ω(1)."

**Formalization Note.** The constants `Cc`, `K`, `ε₀` are chosen before `n` and `f`: wires
`≤ Cc · n²`, every weight **and bias** of absolute value `≤ Cc · n^K`, separation `ε₀ > 0`.
"Depth-two" is `depth ≤ 2`, measured at the output gate. `n ≥ 1`. -/
theorem proposition_4_3 :
    ∃ Cc : ℝ, ∃ K : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ n : ℕ, 1 ≤ n → ∀ f : (Fin n → Bool) → Bool, ShallowSym.IsSymmetric f →
        ∃ C : Circuit n, C.depth ≤ 2 ∧ (C.wires : ℝ) ≤ Cc * (n : ℝ) ^ 2 ∧
          C.ParamsLe (Cc * (n : ℝ) ^ K) ∧ ComputesSep Real.sigmoid C f ε₀ := by sorry

end SigmoidWire
