-- Prove2me | Theorems.Thm_SigmoidWire_Supplement_theorem_5_10
-- name    : SigmoidWire.Supplement.theorem_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:42:52.113183+00:00
-- url     : https://prove2.me/theorems/e0b7f389-7076-4435-9451-be77a195042f
-- title:
--   Theorem 5.10 — depth-three sigmoidal circuits computing $\mathrm{GA}_{n,m}$ need $n^{3/2}/(\log n)^{c_0a}$ bottom gates
-- statement:
--   There is an absolute constant $c_0\ge1$ such that the following holds. Let $a\ge1$, let $n$ be sufficiently large (depending on $a$) with $m=16\lceil\log_2n\cdot\log_2\log_2n\rceil$ dividing $n$, and let $d,W,\delta^{-1}\le n^a$. Suppose that $C$ is a $(2n)$-input layered depth-three sigmoidal circuit in which
--
--   1. the output gate has fan-in at most $d$ and weights in $[-W,W]$;
--   2. the middle layer consists of $d$ sigmoidal gates with weights and biases in $[-W,W]$;
--   3. the bottom layer has $s$ sigmoidal gates in total.
--
--   If $C$ computes the generalized Andreev function $\mathrm{GA}_{n,m}$ (for any irreducible polynomial defining $\mathbb F_{2^{m/2}}$) with separation $\delta\in(0,1)$, then
--   $$s\ \ge\ \frac{n^{3/2}}{(\log n)^{c_0a}}.$$
--
--   This is a super-linear gate lower bound for depth-three sigmoidal circuits with polynomially bounded middle and top layers and unrestricted bottom layer, for a function computable in polynomial time.
--
--   Differences from the source:
--   - encoding: a (2n)-input depth-3 sigmoidal circuit with an output gate, a middle layer of d gates and a bottom layer → IsDepth3Layered C s d W: gates 0..s−1 read inputs only (parameters unbounded), gates s..s+d−1 read inputs and bottom gates (weights and bias in [−W, W]), the output reads only middle gates (weights in [−W, W], bias unbounded); reason: the page bounds exactly these parameters; the middle layer reads inputs (p.30)
--   - generalization: the output gate has fan-in d → fan-in at most d (zero weights are absent wires); reason: covers more circuits; fan-in exactly d is the case of non-zero weights
--   - encoding: n sufficiently large (depending on a); d, W, δ^{−1} ≤ n^a → ∃ c₀ ≥ 1, ∀ a ≥ 1 (real), ∃ N, ∀ n ≥ N; d natural, W and δ real with d, W, δ⁻¹ ≤ n^a and 0 < δ < 1; reason: quantifier order of the page
--   - reading: GA_{n,m} defined when n/m is an integer ("the general case follows by a simple padding argument") → the statement quantifies over the sufficiently large n with gaM n ∣ n; reason: the paper defines GA_{n,m} only for such n and never writes the padded function; there are infinitely many such n
--   - generalization: the field F_{2^ℓ} given by one irreducible polynomial found by [Sho90] → every irreducible P of degree m/2 over GF(2); reason: the proof uses only the field structure; the paper's polynomial is one instance
--   - encoding: binary representations of field elements; y parsed into consecutive blocks → coefficient vectors modulo P (bit j is the coefficient of X^j); block i is {k : k / (n/m) = i}; u = (z_1..z_ℓ), v = (z_{ℓ+1}..z_m); input x then y on Fin (n + n); reason: Lean representation of the same function
--   - encoding: log n in (log n)^{c0·a} → natural logarithm; reason: the existential c₀ absorbs the base for n large depending on a
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 5.10, p.24 (restated p.27)

import Mathlib
import Definitions.Def_SigmoidWire_Circuit
import Definitions.Def_SigmoidWire_ComputesSep
import Definitions.Def_SigmoidWire_Supplement_IsDepth3Layered
import Definitions.Def_SigmoidWire_Supplement_GA

namespace SigmoidWire.Supplement

open SigmoidWire Polynomial

/-- **Theorem 5.10 (gate lower bound for the generalized Andreev function at depth three).**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 5.10, p.24 (PDF p.26), restated p.27 (PDF p.29): "There exists an absolute constant
c0 ≥ 1 such that the following holds. Let a ≥ 1, let n ∈ N be sufficiently large (depending on a),
and d, W, δ^{−1} ≤ n^a. Suppose that C is a (2n)-input depth-3 sigmoidal circuit, where • the output
gate is a sigmoidal gate with fan-in d and weights within [−W, W]; • the middle layer consists of d
sigmoidal gates with weights and biases within [−W, W]; • the bottom layer (i.e. closest to input
variables) has s sigmoidal gates in total. Then if C computes GA_{n,m} with separation δ ∈ (0, 1),
s ≥ n^{3/2}/(log n)^{c0·a}."

**Formalization Note.** The layered circuit is `IsDepth3Layered C s d W` (bottom-layer parameters
and the output bias unbounded). `GA_{n,m}` is defined when `m = gaM n` divides `n`, so the theorem
is stated for those `n` (infinitely many), and for every irreducible `P` of degree `m/2` over
`GF(2)`. `log` is the natural logarithm (a change of base changes only `c₀`, for `n` large). -/
theorem theorem_5_10 :
    ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ a : ℝ, 1 ≤ a → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → gaM n ∣ n →
      ∀ P : (ZMod 2)[X], Irreducible P → P.natDegree = gaM n / 2 →
      ∀ (d : ℕ) (W δ : ℝ), (d : ℝ) ≤ (n : ℝ) ^ a → W ≤ (n : ℝ) ^ a → δ⁻¹ ≤ (n : ℝ) ^ a →
      0 < δ → δ < 1 →
      ∀ (s : ℕ) (C : Circuit (n + n)), IsDepth3Layered C s d W →
        ComputesSep Real.sigmoid C (GA n P) δ →
          (n : ℝ) ^ ((3 : ℝ) / 2) / Real.log n ^ (c₀ * a) ≤ s := by sorry

end SigmoidWire.Supplement
