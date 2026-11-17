-- Prove2me | Theorems.Thm_SigmoidWire_Supplement_theorem_7_3
-- name    : SigmoidWire.Supplement.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:49:08.134762+00:00
-- url     : https://prove2.me/theorems/5f862637-e012-4a1b-a9b6-810f83f13ba7
-- title:
--   Theorem 7.3 — depth-$(d+1)$ threshold circuits by depth-$(d+1)$ sigmoidal circuits of size $\mathrm{poly}(n,s)$ with output weights $\pm1$
-- statement:
--   Let $d\ge1$. There are constants $C,c$ depending only on $d$ such that the following holds. If $f:\{0,1\}^n\to\{0,1\}$ is computed by a threshold circuit (real weights and thresholds) of depth at most $d+1$ and size $s$, then $f$ is computed with no separation by a sigmoidal circuit of depth at most $d+1$ and size at most
--   $$C\big((n+1)(s+1)\big)^c=\mathrm{poly}(n,s)$$
--   whose output gate has weights in $\{\pm1\}$.
--
--   This generalizes Theorem 1.9 to every constant depth.
--
--   Differences from the source:
--   - reading: a depth-(d + 1) circuit C of size s consisting of THR gates → a threshold circuit of depth ≤ d + 1, not necessarily layered, s = T.size + 1; reason: the proof assumes layering "without loss of generality"
--   - encoding: size poly(n, s) → at most C·((n+1)(s+1))^c with C, c depending on d only; reason: a polynomial overhead fixed before n, s, f
--   - reading: output gate weights in {±1} → each output weight is ±1 or 0 (an absent wire); the output bias is free; reason: zero weights are absent wires
--   - reading: a depth-(d + 1) sigmoidal circuit → depth ≤ d + 1 measured at the output; reason: the class reading of depth
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 7.3, p.49

import Mathlib
import Definitions.Def_SigmoidWire_Circuit
import Definitions.Def_SigmoidWire_ComputesSep
import Definitions.Def_SigmoidWire_Supplement_IntWeightsLe
import Definitions.Def_SigmoidWire_Supplement_ThrComputes

namespace SigmoidWire.Supplement

open SigmoidWire

/-- **Theorem 7.3 (depth-(d+1) threshold circuits by depth-(d+1) sigmoidal circuits).**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 7.3, p.49 (PDF p.51): "Let d ≥ 1. Suppose that f : {0,1}^n → {0,1} is computed by a
depth-(d + 1) circuit C of size s consisting of THR gates. Then f is computed with no separation by
a depth-(d + 1) sigmoidal circuit of size poly(n, s), where the output gate has weights in {±1}."

**Formalization Note.** The THR circuit is a threshold circuit (`thrAct`, real weights and
thresholds) of depth at most `d + 1`, not necessarily layered; `s = T.size + 1`. `poly(n, s)` is
`C₀·((n+1)(s+1))^c` with `C₀, c` depending on `d` only. Only the output gate's weights are restricted
(each is `±1`, or `0` for an absent wire). -/
theorem theorem_7_3 :
    ∀ d : ℕ, 1 ≤ d → ∃ C₀ : ℝ, ∃ c : ℕ, ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Circuit n),
      T.depth ≤ d + 1 → ThrComputes T f →
      ∃ C : Circuit n, C.depth ≤ d + 1 ∧
        ((C.size + 1 : ℕ) : ℝ) ≤ C₀ * (((n + 1) * (T.size + 2) : ℕ) : ℝ) ^ c ∧
        OutWeightsPM1 C ∧ ComputesSep Real.sigmoid C f 0 := by sorry

end SigmoidWire.Supplement
