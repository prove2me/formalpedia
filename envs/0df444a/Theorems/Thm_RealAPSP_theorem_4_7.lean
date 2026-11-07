-- Prove2me | Theorems.Thm_RealAPSP_theorem_4_7
-- name    : RealAPSP.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:58:34.162928+00:00
-- url     : https://prove2.me/theorems/bd867892-d83a-46e7-9e00-e4da7d31ffee
-- title:
--   Theorem 4.7 (Poor Man's Freiman's Theorem [FPS26, Theorem 3.10])
-- statement:
--   Let $\Delta\ge0$, $K\ge1$, and let $A\subseteq\mathbb R$ be a nonempty finite set with $|A+A|_{\pm\Delta}\le K|A|_{\pm\Delta}$. Then there is a $\Delta$-approximate subset sum cover of $A$ with rank $(K\log(|A|+2))^{O(1)}$. It can be computed in time $\tilde O(|A|^2)$.
--
--   It converts low doubling, which Lemma 4.5 provides, into the structure Lemma 4.8 can hash. The paper imports this result.
--
--   Differences from the source:
--   - reading: the comparison-addition model of §1.2, p.3, which also names a "realistic" variant → the machine RealAPSP.Machine: the published GuardedSSSP core plus rneg, unit cost, stuck on word overflow, fair coins preloaded in memory; reason: the realistic variant defers to [FPS26, Section 1.1], which is not held, and Theorem 1.1 does not name it; rneg is simulable at constant overhead by pairs p − q
--   - encoding: input and output as mathematical objects → fixed cell layouts for the parameters, matrices and outputs, given in the docstrings; reason: a machine statement needs a layout; every layout used is within a constant factor of any other
--   - encoding: real parameters K ≥ 1 → natural numbers K ≥ 1 in input cells; reason: the integer bank cannot read a real; the statement at the ceiling of a real K implies it at K: the hypothesis on K implies the one on ⌈K⌉, and the bounds at ⌈K⌉ ≤ 2K are within the O-constants
--   - encoding: log |A| → the logarithm of the argument plus 2; reason: the page writes O-notation for large arguments; the literal formula is 0 at small arguments, where a machine needs at least one step
--   - encoding: A ⊆ R with no size condition → A nonempty; reason: Õ(|A|²) is 0 at the empty set
--   - encoding: the real cover vector α → D•α for a scale D chosen with the program; reason: the machine computes only integer combinations of its input reals
--   - reading: "can be computed", not said to be deterministic or randomized → a randomized run with high probability, every failure exponent a; reason: [FPS26] is not held, the paper also leaves its randomized Lemma 5.4 unmarked, and the use inside Lemma 4.9 is randomized; the moderator should check this against [FPS26]
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), Theorem 4.7, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_RealAPSP_Cover

namespace RealAPSP

/-- **Theorem 4.7 (Poor Man's Freiman's Theorem [FPS26, Theorem 3.10]).** Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file sha256 a3dc0096…), p.13 (PDF p.15). Imported; not proved in this paper.

Two clauses with one exponent `c`: the subset sum cover exists, for real `K ≥ 1`; and it is computed in time `Õ(|A|²)`, with `d` at output cell `0`, the bits of `f` from output cell `1`, and `D•α` in real output cells for a scale `D` fixed with the program. -/
theorem theorem_4_7 :
    ∃ c : ℕ,
      (∀ (m : ℕ) (K : ℝ), 1 ≤ m → 1 ≤ K → ∀ Δ : ℝ, 0 ≤ Δ → ∀ a : Fin m → ℝ, Function.Injective a →
        HasDoubling K Δ (valueSet a) →
        ∃ (d : ℕ) (α : Fin d → ℝ) (f : Fin m → Fin d → Bool),
          (d : ℝ) ≤ (K * Real.log ((m : ℝ) + 2)) ^ c ∧ IsSubsetSumCover Δ a d α f) ∧
      ∀ e : ℕ, ∃ (P : Program) (D : ℕ) (κ : ℝ), 1 ≤ D ∧ ∀ (m K : ℕ), 1 ≤ m → 1 ≤ K → ∀ Δ : ℝ, 0 ≤ Δ →
        ∀ a : Fin m → ℝ, Function.Injective a → HasDoubling (K : ℝ) Δ (valueSet a) →
        RunsWhp P (m + K + 2) [(m : ℤ), (K : ℤ)] (Δ :: List.ofFn a)
          (κ * (m : ℝ) ^ 2 * Real.log ((m : ℝ) + 2) ^ κ) ((m : ℝ) ^ (-(e : ℝ))) (fun σ =>
            let d := (σ.imem (outCell 0)).toNat
            (d : ℝ) ≤ ((K : ℝ) * Real.log ((m : ℝ) + 2)) ^ c ∧
            IsSubsetSumCover Δ a d (fun l => σ.rmem (routCell l) / D)
              (fun i l => decide (σ.imem (outCell (1 + (i : ℕ) * d + l)) ≠ 0))) := by sorry

end RealAPSP
