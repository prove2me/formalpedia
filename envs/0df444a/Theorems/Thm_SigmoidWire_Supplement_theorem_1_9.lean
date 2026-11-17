-- Prove2me | Theorems.Thm_SigmoidWire_Supplement_theorem_1_9
-- name    : SigmoidWire.Supplement.theorem_1_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:48:42.999681+00:00
-- url     : https://prove2.me/theorems/549c05ba-8ff9-40a1-94d9-d29890bf22fa
-- title:
--   Theorem 1.9 — $\mathrm{THR}\circ\mathrm{THR}$ by depth-two sigmoidal circuits of size $s\cdot\mathrm{poly}(n)$ with output weights $\pm1$
-- statement:
--   There are absolute constants $C,c$ such that the following holds. If $f:\{0,1\}^n\to\{0,1\}$ is computed by a $\mathrm{THR}\circ\mathrm{THR}$ circuit (real weights and thresholds) of size $s$, then $f$ is computed with no separation by a depth-two sigmoidal circuit of size at most
--   $$C\,s\,(n+1)^c=s\cdot\mathrm{poly}(n)$$
--   whose output gate has weights in $\{\pm1\}$.
--
--   Depth-two sigmoidal circuits with a $\pm1$-weighted output gate are thus at least as strong as depth-two threshold circuits, at polynomial cost.
--
--   Differences from the source:
--   - reading: a THR ◦ THR circuit of size s → a threshold circuit of depth ≤ 2 (the output may read inputs), real weights and thresholds, s = T.size + 1 gates; reason: the proof (p.48) removes direct input wires to the output "without loss of generality", so the class allows them
--   - encoding: size s · poly(n) → at most C·s·(n+1)^c with absolute C, c; reason: a polynomial overhead fixed before n, s, f
--   - reading: a depth-two sigmoidal circuit → a sigmoidal circuit of depth ≤ 2 measured at the output; the output may read inputs; reason: the class reading of depth-two circuits used in §6 (p.38, p.41)
--   - reading: output gate weights in {±1} → each output weight is ±1 or 0 (an absent wire); the output bias is free; reason: zero weights are absent wires
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 1.9, p.6; restated with its proof in §7.2, pp.48–49

import Mathlib
import Definitions.Def_SigmoidWire_Circuit
import Definitions.Def_SigmoidWire_ComputesSep
import Definitions.Def_SigmoidWire_Supplement_IntWeightsLe
import Definitions.Def_SigmoidWire_Supplement_ThrComputes

namespace SigmoidWire.Supplement

open SigmoidWire

/-- **Theorem 1.9 (THR ∘ THR by depth-two sigmoidal circuits with output weights `±1`).**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 1.9, p.6 (PDF p.8), restated with its proof in §7.2, p.48 (PDF p.50): "Suppose that
f : {0,1}^n → {0,1} is computed by a THR ◦ THR circuit of size s. Then f is computed with no
separation by a depth-two sigmoidal circuit of size s · poly(n) whose output gate has weights in
{±1}."

**Formalization Note.** A THR ∘ THR circuit is a threshold circuit (`thrAct`, real weights and
thresholds) of depth at most `2`: a layer of THR gates and a THR output gate, which may also read
inputs (the proof, p.48, removes such wires "without loss of generality"). `s = T.size + 1` counts
all gates. `s · poly(n)` is `C₀·s·(n+1)^c` with absolute `C₀, c`. Only the output gate's weights are
restricted (each is `±1`, or `0` for an absent wire); every other parameter is a real number. -/
theorem theorem_1_9 :
    ∃ C₀ : ℝ, ∃ c : ℕ, ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Circuit n),
      T.depth ≤ 2 → ThrComputes T f →
      ∃ C : Circuit n, C.depth ≤ 2 ∧
        ((C.size + 1 : ℕ) : ℝ) ≤ C₀ * ((T.size + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ c ∧
        OutWeightsPM1 C ∧ ComputesSep Real.sigmoid C f 0 := by sorry

end SigmoidWire.Supplement
