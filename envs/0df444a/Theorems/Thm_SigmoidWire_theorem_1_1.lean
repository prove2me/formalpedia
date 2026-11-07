-- Prove2me | Theorems.Thm_SigmoidWire_theorem_1_1
-- name    : SigmoidWire.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:07:57.497189+00:00
-- url     : https://prove2.me/theorems/88bbe96f-9520-4351-ad4b-6545bc99712c
-- title:
--   Theorem 1.1: wire complexity of symmetric functions and parity for robust sigmoidal circuits
-- statement:
--   The theorem has three parts.
--
--   1. There are constants $C,K,\varepsilon_0>0$ such that for every $n\ge1$ and every symmetric $f:\{0,1\}^n\to\{0,1\}$ there is a sigmoidal circuit of depth at most $3$ with at most $Cn$ wires and all weights and biases at most $Cn^K$ in absolute value, computing $f$ with separation $\varepsilon_0$.
--   2. The same holds with depth at most $2$ and at most $Cn^2$ wires.
--   3. For every $K$ there is a constant $c>0$ such that for all $n\ge2$, every sigmoidal circuit of depth at most $2$ with all weights and biases in $[-n^K,n^K]$ that computes parity $\oplus_n$ with separation $n^{-K}$ has at least
--
--   $$
--   \frac{c\,n^2}{\log^2n}
--   $$
--
--   wires.
--
--   The upper bound in part 1 contrasts with threshold circuits, where parity needs super-linearly many wires at every constant depth. Parts 2 and 3 settle the depth-two wire complexity of parity up to the factor $\log^2 n$.
--
--   **Formalization Note** A robust circuit has polynomially bounded weights and biases and noticeable separation. Wires are non-zero weights over all gates, including wires from inputs to the output gate.
--
--   Differences from the source:
--   - generalization: "robust": noticeable separation Ω(n^{−k}), in parts 1–2 → a constant separation ε₀ > 0; reason: Theorem 4.1 and Proposition 4.3 give Ω(1); a constant separation is noticeable
--   - reading: "depth-3", "depth-2" → depth ≤ 3, depth ≤ 2, measured at the output gate along non-zero weights; reason: the class reading of depth-d circuits, and in part 3 the most general one
--   - reading: "wires (i.e. non-zero parameters)" → non-zero weights; biases are not wires; reason: the count "n + n + n" on p.19 counts fan-ins only
--   - reading: polynomially bounded weights and biases, noticeable separation → Cc·n^K in parts 1–2; n^K and n^{−K} with one K in part 3; reason: for n ≥ 2 every bound a·n^k and b·n^{−k} has this form for a larger K
--   - encoding: O(·), Ω(·) for large n → constants before n, for all n ≥ 1 (parts 1–2) and n ≥ 2 (part 3); reason: constants absorb small n, and log 1 = 0 is excluded; this is not a narrowing
--   - encoding: log, base unspecified → natural logarithm; reason: the base changes only the constant
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 1.1, p.3

import Mathlib
import Definitions.Def_ShallowSym_IsSymmetric
import Definitions.Def_SigmoidWire_Circuit
import Definitions.Def_SigmoidWire_ComputesSep
import Definitions.Def_GeoQAC_parityFn

namespace SigmoidWire

/-- **Theorem 1.1 (wire complexity of symmetric functions and parity for robust sigmoidal
circuits).**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 1.1, p.3 (PDF p.5):
"Every symmetric Boolean function (including parity) is computable by a depth-3 robust sigmoidal
circuit with O(n) wires. Any symmetric function (including parity) is computable by a depth-2 robust
sigmoidal circuit with O(n²) wires, and least Ω(n²/log² n) wires are required for parity in the same
model."

**Formalization Note.** "Robust" (p.3) = polynomially bounded weights and biases and noticeable
separation (Definition 3.1). The three conjuncts:
1. constants `Cc, K, ε₀ > 0` before `n ≥ 1` and the symmetric `f`: a circuit of depth `≤ 3` with
   `≤ Cc·n` wires, all weights and biases in `[−Cc·n^K, Cc·n^K]`, separation `ε₀` (a constant, which
   is stronger than noticeable);
2. the same with depth `≤ 2` and `≤ Cc·n²` wires;
3. for every `K` there is `c > 0` such that for all `n ≥ 2`, every circuit of depth `≤ 2` with all
   weights and biases in `[−n^K, n^K]` computing parity with separation `n^{−K}` has at least
   `c·n²/(log n)²` wires (for `n ≥ 2`, every polynomial bound and noticeable separation is of this
   form for a larger `K`).

Depth is measured at the output gate; wires are the non-zero weights; `log` is the natural
logarithm; parity is the published `GeoQAC.parityFn n`. -/
theorem theorem_1_1 :
    (∃ Cc : ℝ, ∃ K : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ n : ℕ, 1 ≤ n → ∀ f : (Fin n → Bool) → Bool, ShallowSym.IsSymmetric f →
        ∃ C : Circuit n, C.depth ≤ 3 ∧ (C.wires : ℝ) ≤ Cc * n ∧
          C.ParamsLe (Cc * (n : ℝ) ^ K) ∧ ComputesSep Real.sigmoid C f ε₀) ∧
    (∃ Cc : ℝ, ∃ K : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ n : ℕ, 1 ≤ n → ∀ f : (Fin n → Bool) → Bool, ShallowSym.IsSymmetric f →
        ∃ C : Circuit n, C.depth ≤ 2 ∧ (C.wires : ℝ) ≤ Cc * (n : ℝ) ^ 2 ∧
          C.ParamsLe (Cc * (n : ℝ) ^ K) ∧ ComputesSep Real.sigmoid C f ε₀) ∧
    (∀ K : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → ∀ C : Circuit n,
      C.depth ≤ 2 → C.ParamsLe ((n : ℝ) ^ K) →
        ComputesSep Real.sigmoid C (GeoQAC.parityFn n) (((n : ℝ) ^ K)⁻¹) →
          c * (n : ℝ) ^ 2 / Real.log n ^ 2 ≤ C.wires) := by sorry

end SigmoidWire
