-- Prove2me | Theorems.Thm_SigmoidWire_Supplement_theorem_1_8
-- name    : SigmoidWire.Supplement.theorem_1_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:47:43.394235+00:00
-- url     : https://prove2.me/theorems/08a1153f-5d89-4ca2-8105-88e347c7baae
-- title:
--   Theorem 1.8 — depth-two sigmoidal circuits with integer weights in $[-W,W]$, biases in $(-1,1)$ and no separation are equivalent to $\mathrm{THR}\circ\mathrm{MAJ}$
-- statement:
--   There are a threshold $N$ and constants $C_1,C_2,c_1,c_2$ such that for all $n\ge N$, all integers $W\ge1$, all $s$ and every Boolean function $f:\{0,1\}^n\to\{0,1\}$:
--
--   1. if $f$ is computed with no separation by a depth-two sigmoidal circuit of size at most $s$ whose weights are all integers in $[-W,W]$ and whose biases all lie in $(-1,1)$, then $f$ is computed by a $\mathrm{THR}\circ\mathrm{MAJ}$ circuit with MAJ weights in $\{-W,\dots,W\}$ of size at most $C_1\,s\,((n+1)(W+1))^{c_1}$;
--   2. if $f$ is computed by such a $\mathrm{THR}\circ\mathrm{MAJ}$ circuit of size at most $s$, then $f$ is computed with no separation by a depth-two sigmoidal circuit of size at most $C_2\,s\,((n+1)(W+1))^{c_2}$ whose weights are all integers in $[-W,W]$, whose biases all lie in $(-1,1)$, and whose output gate has weights in $\{\pm1\}$.
--
--   Hence the two models are equivalent up to a factor $\mathrm{poly}(n,W)$ in size, and the output gate of the sigmoidal circuit can be taken with weights $\pm1$.
--
--   Differences from the source:
--   - encoding: equivalence of (1) and (2) at size s · poly(n, W), s = s(n), W = W(n) ≥ 1 → two implications, each from size ≤ s to size ≤ C·s·((n+1)(W+1))^c with C, c fixed before n, W, s, f; W ranges over all naturals ≥ 1; reason: composing with any s·p(n, W) gives the stated equivalence for every pair of functions s(n), W(n)
--   - encoding: n sufficiently large → ∃ N ∀ n ≥ N; reason: quantifier of the page
--   - reading: a THR ◦ MAJ circuit whose bottom MAJ gates have weight from {−W, …, W} → IsTHRoMAJ T 1 W: non-output gates with integer weights in [−W, W] and real thresholds, a THR output with real weights and threshold reading only gates; size T.size + 1; reason: f(x) = I[Σ α_i G_i(x) ≥ θ] as in the proof (p.47)
--   - reading: a depth-two sigmoidal circuit → a sigmoidal circuit of depth ≤ 2 measured at the output; the output may read inputs; reason: the class reading of depth-two circuits used in §6 (p.38, p.41)
--   - reading: output gate weights in {±1} → each output weight is ±1 or 0 (an absent wire); the output bias is free; reason: zero weights are absent wires
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 1.8, p.6; restated with its proof in §7.1, pp.46–48

import Mathlib
import Definitions.Def_SigmoidWire_Circuit
import Definitions.Def_SigmoidWire_ComputesSep
import Definitions.Def_SigmoidWire_Supplement_IntWeightsLe
import Definitions.Def_SigmoidWire_Supplement_ThrComputes
import Definitions.Def_SigmoidWire_Supplement_IsTHRoMAJ

namespace SigmoidWire.Supplement

open SigmoidWire

/-- **Theorem 1.8 (small-integer-weight depth-two sigmoidal circuits with no separation are
THR ∘ MAJ).**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 1.8, p.6 (PDF p.8), restated with its proof in §7.1, p.46 (PDF p.48): "Let n ∈ N be
sufficiently large and s = s(n), W = W(n) ≥ 1 be functions, and f : {0,1}^n → {0,1} be a Boolean
function. The following two statements are equivalent: (1) f can be computed by a depth-two
sigmoidal circuit of size s · poly(n, W) with no separation, where all weights are integers in
[−W, W] and all biases are real numbers in (−1, 1). (2) f can be computed by a THR ◦ MAJ circuit of
size s · poly(n, W), where the bottom MAJ gates have weight taken from {−W, …, W}. Moreover, the
output gate of the circuit in (1) can be assumed to have weights in {±1}."

**Formalization Note.** The equivalence up to `s · poly(n, W)` is stated as two implications with
polynomial overheads fixed before `n, W, s, f`: a circuit of type (1) of size at most `s` gives one
of type (2) of size at most `C₁·s·((n+1)(W+1))^{c₁}`, and a circuit of type (2) of size at most `s`
gives one of type (1) of size at most `C₂·s·((n+1)(W+1))^{c₂}` whose output gate has weights in
`{±1}`; composing with any `s·p(n, W)` yields the stated equivalence. "n sufficiently large" is
`∃ N, ∀ n ≥ N`. Sizes count all gates (`C.size + 1`). Type (1): a sigmoidal circuit of depth at most
`2`, every weight an integer in `[−W, W]` (`IntWeightsLe`), every bias in `(−1, 1)`
(`BiasesInUnit`), no separation. Type (2): `IsTHRoMAJ T 1 W` evaluated with threshold gates
(`ThrComputes`): MAJ gates with integer weights in `{−W, …, W}` and real thresholds under a THR gate
with real weights and threshold. `W` is a natural number `≥ 1`. -/
theorem theorem_1_8 :
    ∃ N : ℕ, ∃ C₁ C₂ : ℝ, ∃ c₁ c₂ : ℕ, ∀ n : ℕ, N ≤ n → ∀ W : ℕ, 1 ≤ W → ∀ s : ℕ,
      ∀ f : (Fin n → Bool) → Bool,
      ((∃ C : Circuit n, C.depth ≤ 2 ∧ C.size + 1 ≤ s ∧ IntWeightsLe C W ∧ BiasesInUnit C ∧
          ComputesSep Real.sigmoid C f 0) →
        ∃ T : Circuit n, IsTHRoMAJ T 1 W ∧
          ((T.size + 1 : ℕ) : ℝ) ≤ C₁ * s * (((n + 1) * (W + 1) : ℕ) : ℝ) ^ c₁ ∧
          ThrComputes T f) ∧
      ((∃ T : Circuit n, IsTHRoMAJ T 1 W ∧ T.size + 1 ≤ s ∧ ThrComputes T f) →
        ∃ C : Circuit n, C.depth ≤ 2 ∧
          ((C.size + 1 : ℕ) : ℝ) ≤ C₂ * s * (((n + 1) * (W + 1) : ℕ) : ℝ) ^ c₂ ∧
          IntWeightsLe C W ∧ BiasesInUnit C ∧ OutWeightsPM1 C ∧
          ComputesSep Real.sigmoid C f 0) := by sorry

end SigmoidWire.Supplement
