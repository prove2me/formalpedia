-- Prove2me | Theorems.Thm_SigmoidWire_Supplement_theorem_5_19
-- name    : SigmoidWire.Supplement.theorem_5_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:44:04.598921+00:00
-- url     : https://prove2.me/theorems/010da862-032a-48a5-b4ba-fa57a8cbfde9
-- title:
--   Theorem 5.19 — small polynomial-weight depth-$d$ sigmoidal circuits have correlation $s^{1-1/d}n^{-1/(2d)+o(1)}$ with parity
-- statement:
--   Let $a,d\ge1$ and let $n$ be sufficiently large. Let $C:\{0,1\}^n\to[0,1]$ be a sigmoidal circuit of depth at most $d$ with $s$ gates whose gate-to-gate weights lie in $[-n^a,n^a]$. Then for all $0\le\delta_0<\delta_1\le1$ with $\delta_1-\delta_0\ge n^{-a}$,
--   $$\Pr_{x}\big[C(x)>\delta_1\wedge\oplus_n(x)=1\big]+\Pr_{x}\big[C(x)<\delta_0\wedge\oplus_n(x)=0\big]\ \le\ \frac12+s^{1-1/d}\cdot n^{-1/(2d)+o(1)},$$
--   where $x$ is uniform on $\{0,1\}^n$ and the $o(1)$ term depends only on $a$ and $d$.
--
--   In particular, for $d\ge2$ and every $\gamma>0$ there is $\eta>0$ such that, for $n$ sufficiently large, if $s\le n^{1/(2(d-1))-\gamma}$ and $C$ computes a Boolean function $f$ with separation at least $n^{-a}$, then
--   $$\mathrm{Cor}(f,\oplus_n)\le n^{-\eta}.$$
--
--   This matches the known correlation bounds for linear threshold circuits with parity.
--
--   Differences from the source:
--   - generalization: weights within [−n^a, n^a] → only the gate-to-gate weights are in [−n^a, n^a] (GateWeightsLe); input weights and biases are arbitrary; reason: the weights of a polynomial-adjusted circuit (Definition 5.27, p.34), the model Lemma 5.28 is proved for; circuits with all weights bounded are a special case
--   - reading: a depth-d sigmoidal circuit with s gates → depth ≤ d (measured at the output), s = C.size + 1 counting every gate; reason: the bound is non-decreasing in d and s
--   - encoding: s^{1−1/d} · n^{−1/(2d)+o(1)} for sufficiently large n → ∀ ε > 0 ∃ N ∀ n ≥ N with exponent −1/(2d) + ε; reason: the o(1) depends on a and d only
--   - encoding: s ≤ n^{1/(2(d−1))−Ω(1)} and Cor(f, ⊕n) ≤ n^{−Ω(1)} → ∀ γ > 0 ∃ η > 0 ∃ N: s ≤ n^{1/(2(d−1))−γ} implies Cor ≤ n^{−η}; reason: the standard meaning of the two Ω(1)
--   - encoding: separation at least n^{−a} → ComputesSep with separation n^{−a}; reason: every larger separation implies it
--   - encoding: Pr over x ← {0,1}^n → number of points divided by 2^n; a real, d natural; reason: uniform distribution
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 5.19, p.31 (restated p.37)

import Mathlib
import Definitions.Def_SigmoidWire_Circuit
import Definitions.Def_SigmoidWire_ComputesSep
import Definitions.Def_GeoQAC_parityFn
import Definitions.Def_SigmoidWire_Supplement_GateWeightsLe
import Definitions.Def_SigmoidWire_Supplement_cor

namespace SigmoidWire.Supplement

open SigmoidWire

open Classical in
/-- **Theorem 5.19 (correlation of small polynomial-weight sigmoidal circuits with parity).**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 5.19, p.31 (PDF p.33), restated p.37 (PDF p.39): "For any a, d ≥ 1 and sufficiently
large n, let C : {0,1}^n → [0,1] be any depth-d sigmoidal circuit with s gates and weights within
[−n^a, n^a]. Then for any 0 ≤ δ0 < δ1 ≤ 1 with δ1 − δ0 ≥ n^{−a}, we have
Pr_x[C(x) > δ1 ∧ ⊕n(x) = 1] + Pr_x[C(x) < δ0 ∧ ⊕n(x) = 0] ≤ 1/2 + s^{1−1/d} · n^{−1/(2d)+o(1)}.
In particular, for d ≥ 2 and s ≤ n^{1/(2(d−1))−Ω(1)}, if C computes a Boolean function f with
separation at least n^{−a}, then Cor(f, ⊕n) ≤ n^{−Ω(1)}."

**Formalization Note.** Conjunct 1: the `o(1)` depends on `a, d` only, so it is "for every `ε > 0`
there is `N`" with exponent `−1/(2d) + ε`. Conjunct 2: for every `γ > 0` (the `Ω(1)` in the size
bound) there is `η > 0` (the `Ω(1)` in the conclusion). `s = C.size + 1` counts every gate; depth
is at most `d`; probabilities are counts over `{0,1}^n` divided by `2^n`. Only the gate-to-gate
weights are bounded (`GateWeightsLe`, the weights of Definition 5.27); input weights and biases are
arbitrary. Separation at least `n^{−a}` is `ComputesSep … (n^{−a})`, which every larger separation
implies. Parity is the published `GeoQAC.parityFn`. -/
theorem theorem_5_19 :
    (∀ a : ℝ, 1 ≤ a → ∀ d : ℕ, 1 ≤ d → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ C : Circuit n, C.depth ≤ d → GateWeightsLe C ((n : ℝ) ^ a) →
      ∀ δ₀ δ₁ : ℝ, 0 ≤ δ₀ → δ₀ < δ₁ → δ₁ ≤ 1 → (n : ℝ) ^ (-a) ≤ δ₁ - δ₀ →
        ((Finset.univ.filter fun x : Fin n → Bool =>
            δ₁ < C.eval Real.sigmoid x ∧ GeoQAC.parityFn n x = true).card : ℝ) / 2 ^ n +
          ((Finset.univ.filter fun x : Fin n → Bool =>
            C.eval Real.sigmoid x < δ₀ ∧ GeoQAC.parityFn n x = false).card : ℝ) / 2 ^ n ≤
          1 / 2 + ((C.size + 1 : ℕ) : ℝ) ^ (1 - 1 / (d : ℝ)) *
            (n : ℝ) ^ (-(1 / (2 * (d : ℝ))) + ε)) ∧
    (∀ a : ℝ, 1 ≤ a → ∀ d : ℕ, 2 ≤ d → ∀ γ : ℝ, 0 < γ → ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → ∀ C : Circuit n, C.depth ≤ d → GateWeightsLe C ((n : ℝ) ^ a) →
      ((C.size + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 / (2 * ((d : ℝ) - 1)) - γ) →
      ∀ f : (Fin n → Bool) → Bool, ComputesSep Real.sigmoid C f ((n : ℝ) ^ (-a)) →
        cor f (GeoQAC.parityFn n) ≤ (n : ℝ) ^ (-η)) := by sorry

end SigmoidWire.Supplement
