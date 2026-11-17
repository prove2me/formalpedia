-- Prove2me | Theorems.Thm_SigmoidWire_Supplement_theorem_6_1
-- name    : SigmoidWire.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:45:11.793107+00:00
-- url     : https://prove2.me/theorems/92b4f383-599f-4fc3-ae67-dbd10a61229b
-- title:
--   Theorem 6.1 — depth-two sigmoidal circuits with no separation keep their architecture with parameters at most $(h(n+1)+1)^{O(h(n+2)+1)}$
-- statement:
--   There is an absolute constant $K$ such that the following holds. Suppose that $f:\{0,1\}^n\to\{0,1\}$ is computed with no separation by a depth-two sigmoidal circuit with $h\ge1$ gates in the bottom layer (the output gate may also read input variables). Then $f$ is computed with no separation by a circuit with the same architecture — the same gates and exactly the same set of non-zero weights — all of whose weights and biases have absolute value at most
--   $$(h(n+1)+1)^{K(h(n+2)+1)}\;=\;2^{O(hn\log(hn))}.$$
--
--   Unlike threshold gates, sigmoidal gates have non-Boolean outputs, so the classical weight bounds for threshold circuits do not apply; this theorem gives such a bound at depth two while keeping the gate count.
--
--   Differences from the source:
--   - encoding: a depth-2 sigmoidal circuit with h ≥ 1 gates in the bottom layer → IsDepth2Layered C h: h bottom gates reading inputs only, an output gate reading bottom gates and inputs; reason: the proof writes the output pre-activation as c(x) + Σ v_i σ(…) with direct input wires u_j (p.38)
--   - reading: the same architecture → same gate set and, for every weight, non-zero in the new circuit iff non-zero in the old one; reason: the proof (p.39) sets absent wires to 0 and fixes the sign of every present parameter
--   - reading: weights and biases have absolute values at most … → every weight and every bias of every gate; reason: the proof bounds bottom and top parameters, including c₀
--   - encoding: (h(n + 1) + 1)^{O(h(n+2)+1)} = 2^{O(hn log(hn))} → (h(n+1)+1)^{K·(h(n+2)+1)} with one absolute K chosen before n, h, f, C; reason: the O(·) of [BPR96] is absolute; the second form restates the same bound
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 6.1, p.38

import Mathlib
import Definitions.Def_SigmoidWire_Circuit
import Definitions.Def_SigmoidWire_ComputesSep
import Definitions.Def_SigmoidWire_Supplement_IsDepth2Layered

namespace SigmoidWire.Supplement

open SigmoidWire

/-- **Theorem 6.1 (architecture-preserving weight bound at depth two).**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 6.1, p.38 (PDF p.40): "Suppose that f : {0,1}^n → {0,1} is computed by a depth-2
sigmoidal circuit with h ≥ 1 gates in the bottom layer and no separation. Then f is computed by a
circuit with the same architecture whose weights and biases have absolute values at most
(h(n + 1) + 1)^{O(h(n+2)+1)} = 2^{O(hn log(hn))} with no separation."

**Formalization Note.** The circuit is `IsDepth2Layered C h` (bottom gates read inputs only; the
output may read inputs directly). "Same architecture": the new circuit has the same gates and the
same set of wires, i.e. a weight is non-zero in it iff it is non-zero in `C` (the proof, p.39, fixes
the sign of every present parameter). The bound applies to every weight and every bias. The `O(·)`
is one absolute constant `K`, chosen before `n`, `h`, `f` and `C`; the form `2^{O(hn log(hn))}` is a
restatement of the same bound. "No separation" is `ComputesSep … 0` for both circuits. -/
theorem theorem_6_1 :
    ∃ K : ℝ, ∀ (n h : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit n), 1 ≤ h →
      IsDepth2Layered C h → ComputesSep Real.sigmoid C f 0 →
      ∃ (w' : (j : Fin (C.size + 1)) → (Fin n ⊕ Fin j) → ℝ) (b' : Fin (C.size + 1) → ℝ),
        (∀ j src, w' j src ≠ 0 ↔ C.weight j src ≠ 0) ∧
        (∀ j src, |w' j src| ≤ ((h * (n + 1) + 1 : ℕ) : ℝ) ^ (K * ((h * (n + 2) + 1 : ℕ) : ℝ))) ∧
        (∀ j, |b' j| ≤ ((h * (n + 1) + 1 : ℕ) : ℝ) ^ (K * ((h * (n + 2) + 1 : ℕ) : ℝ))) ∧
        ComputesSep Real.sigmoid (⟨C.size, w', b'⟩ : Circuit n) f 0 := by sorry

end SigmoidWire.Supplement
