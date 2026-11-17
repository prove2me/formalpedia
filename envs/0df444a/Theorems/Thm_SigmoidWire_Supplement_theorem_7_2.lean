-- Prove2me | Theorems.Thm_SigmoidWire_Supplement_theorem_7_2
-- name    : SigmoidWire.Supplement.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:48:19.6778+00:00
-- url     : https://prove2.me/theorems/c4cfa2a6-ed28-4e4d-858e-f4b0bf48ebdc
-- title:
--   Theorem 7.2 — $\mathrm{THR}\circ\mathrm{MAJ}_d$ by depth-$(d+1)$ sigmoidal circuits with integer weights in $[-W,W]$ and biases in $(-1,1)$
-- statement:
--   Let $d\ge1$. There are constants $C,c$ depending only on $d$ such that for all $n$ and $W\in\mathbb N$: if $f:\{0,1\}^n\to\{0,1\}$ is computed by a $\mathrm{THR}\circ\mathrm{MAJ}_d$ circuit of size $s$ whose MAJ gates have integer weights in $[-W,W]$, then $f$ is computed with no separation by a sigmoidal circuit of depth at most $d+1$ and size at most
--   $$C\big((n+1)(s+1)(W+1)\big)^c=\mathrm{poly}(n,s,W)$$
--   in which every gate has integer weights in $[-W,W]$ and bias in $(-1,1)$.
--
--   This extends the direction (2) ⇒ (1) of Theorem 1.8 to larger depth.
--
--   Differences from the source:
--   - encoding: size poly(n, s, W) → at most C·((n+1)(s+1)(W+1))^c with C, c depending on d only, s = T.size + 1; reason: a polynomial overhead fixed before n, s, W
--   - reading: a THR ◦ MAJ_d circuit → IsTHRoMAJ T d W: MAJ gates (integer weights in [−W, W], real thresholds), a THR output reading only gates, depth ≤ d + 1, not necessarily layered; reason: the proof assumes layering "without loss of generality"
--   - reading: a depth-(d + 1) sigmoidal circuit → depth ≤ d + 1 measured at the output; reason: the class reading of depth
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 7.2, p.48

import Mathlib
import Definitions.Def_SigmoidWire_Circuit
import Definitions.Def_SigmoidWire_ComputesSep
import Definitions.Def_SigmoidWire_Supplement_IntWeightsLe
import Definitions.Def_SigmoidWire_Supplement_ThrComputes
import Definitions.Def_SigmoidWire_Supplement_IsTHRoMAJ

namespace SigmoidWire.Supplement

open SigmoidWire

/-- **Theorem 7.2 (THR ∘ MAJ_d by depth-(d+1) small-weight sigmoidal circuits).**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 7.2, p.48 (PDF p.50): "Let d ≥ 1 and W ∈ N. Suppose that f : {0,1}^n → {0,1} is
computed by a THR ◦ MAJ_d circuit C of size s in which the MAJ gates have integer weights in
[−W, W]. Then f is computed with no separation by a depth-(d + 1) sigmoidal circuit of size
poly(n, s, W) in which all gates have integer weights in [−W, W] and biases in (−1, 1)."

**Formalization Note.** The THR ∘ MAJ_d circuit is `IsTHRoMAJ T d W` with `ThrComputes T f`
(not necessarily layered); `s = T.size + 1`. `poly(n, s, W)` is `C₀·((n+1)(s+1)(W+1))^c` with
`C₀, c` depending on `d` only. In the sigmoidal circuit every gate, the output included, has
integer weights in `[−W, W]` and bias in `(−1, 1)`; its depth is at most `d + 1`. `W = 0` is
allowed (then `f` is constant). -/
theorem theorem_7_2 :
    ∀ d : ℕ, 1 ≤ d → ∃ C₀ : ℝ, ∃ c : ℕ, ∀ (n W : ℕ) (f : (Fin n → Bool) → Bool) (T : Circuit n),
      IsTHRoMAJ T d W → ThrComputes T f →
      ∃ C : Circuit n, C.depth ≤ d + 1 ∧
        ((C.size + 1 : ℕ) : ℝ) ≤ C₀ * (((n + 1) * (T.size + 2) * (W + 1) : ℕ) : ℝ) ^ c ∧
        IntWeightsLe C W ∧ BiasesInUnit C ∧ ComputesSep Real.sigmoid C f 0 := by sorry

end SigmoidWire.Supplement
