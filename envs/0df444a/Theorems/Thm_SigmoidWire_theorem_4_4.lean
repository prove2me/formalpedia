-- Prove2me | Theorems.Thm_SigmoidWire_theorem_4_4
-- name    : SigmoidWire.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:07:36.496049+00:00
-- url     : https://prove2.me/theorems/051f4cff-009c-4a29-bd3e-f35bd4c0b0cf
-- title:
--   Theorem 4.4: depth-two $\sigma$-circuits are sign-represented by rational functions of low degree (corrected: $\max(\kappa,1)$ in the logarithm)
-- statement:
--   Let $c>0$ and $c_0\ge1$. There is a constant $C_*$, depending only on $c,c_0$, with the following property. Let $\sigma:\mathbb R\to[0,1]$ be non-decreasing and $\kappa$-Lipschitz, $\kappa\ge0$, and suppose that for all integers $k\ge1$ and reals $a\ge1$ there is a rational function $r_k$ of degree at most $k$ with no pole in $[-a,a]$ such that $|r_k(x)-\sigma(x)|\le c_0a^{c_0}e^{-k^{1/c}/c_0}$ for every $x\in[-a,a]$.
--
--   Then for every $\sigma$-circuit $C$ on $n$ inputs of depth at most $2$, with weights and biases in $[-W,W]$ and at most $E$ wires, that computes $f:\{0,1\}^n\to\{0,1\}$ with separation $\delta>0$, there is a rational function $r$ of degree at most
--
--   $$
--   C_*\,\sqrt E\;\log^{c/2}\Bigl(2+\frac{n\max(\kappa,1)EW}{\delta}\Bigr)
--   $$
--
--   that sign-represents $f$, i.e. $f(x)=\mathrm{sgn}(r(x))$ on $\{0,1\}^n$.
--
--   Together with the degree lower bound for parity, this turns a depth-two circuit into a wire lower bound.
--
--   **Formalization Note** The source prints $\log^{c/2}(n\kappa EW/\delta)$. The two agree up to the constant when $\kappa\ge1$, and for every fixed $\kappa>0$ the bound above is the printed one with a constant depending also on $\kappa$. The paper uses only $\kappa=1/4$.
--
--   Differences from the source:
--   - correction: O(√E log^{c/2}(nκEW/δ)) with c, c₀ the only constants → log(2 + n·max(κ,1)·E·W/δ), Cst depending only on c, c₀; reason: the printed form is false for small κ: for c = 4, c₀ = 1, the function σ(x) = p(Sigmoid(x/W)), with p a monotone polynomial staircase of slope ≤ 1 depending on n and W huge, satisfies every assumption with κW bounded; a circuit with O(n) wires computes parity with separation Ω(1/n); the printed bound would give degree O(√n log²n) < n/2, contradicting Corollary 4.6's degree bound for parity. The proof sketch's k = Θ(log^c(nκEW/δ)) needs log(nW) = O(log(nκEW/δ)), which fails there
--   - reading: log(nκEW/δ), which may be ≤ 0 → log(2 + …), which is ≥ log 2 > 0; reason: an O(·) with a non-positive logarithm is meaningless; the two agree up to a constant when the printed log is bounded away from 0
--   - reading: "depth-two" → depth ≤ 2, measured at the output gate along non-zero weights; reason: the class reading of depth-d circuits; a shallower circuit is not excluded
--   - encoding: "log(…/δ)" and κ-Lipschitz → 0 < δ and 0 ≤ κ, Lipschitz as |σ x − σ y| ≤ κ|x − y|; reason: needed for the printed expression; no instance is lost
--   - reading: "wires (i.e. non-zero parameters)" (p.3) → non-zero weights; biases are not wires; reason: the count "n + n + n" on p.19 counts fan-ins only; a gate with no incoming wire is a constant that folds into its readers' biases, so the two counts agree up to a constant factor
--   - encoding: log, base unspecified → natural logarithm; reason: the base changes only the constant
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 4.4, p.19; proof sketch, p.20

import Mathlib
import Definitions.Def_SigmoidWire_Circuit
import Definitions.Def_SigmoidWire_ComputesSep
import Definitions.Def_SigmoidWire_SignRepBy
import Definitions.Def_SigmoidWire_RatApproxOn

namespace SigmoidWire

/-- **Theorem 4.4 (adapted from [PS94, Theorem 3]): depth-two σ-circuits are sign-represented by
rational functions of degree `O(√E log^{c/2}(nκEW/δ))`.**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 4.4, p.19 (PDF p.21):
"Let c > 0, c₀ ≥ 1 be constants, and σ : R → [0, 1] be any non-decreasing κ-Lipschitz function
satisfying the following conditions: For every k ≥ 1, a ≥ 1, there is a rational function r_k(x) of
degree at most k with no pole in [−a, a] such that for every x ∈ [−a, a],
|r_k(x) − σ(x)| ≤ c₀a^{c₀} · e^{−k^{1/c}/c₀}. Then for any depth-two σ-circuit C : {0, 1}^n → [0, 1]
with weights and biases within [−W, W] and has at most E wires, if C computes a Boolean function
f : {0, 1}^n → {0, 1} with separation δ, there is a rational function r : {0, 1}^n → R of degree
O(√E log^{c/2}(nκEW/δ)) that sign-represent f, i.e., f(x) = sgn(r(x)) for every x ∈ {0, 1}^n."

**Correction.** The printed logarithm is `log(nκEW/δ)`. For `κ ≥ 1` the bound below is exactly that
bound, with a constant depending only on `c, c₀`. For small `κ` the proof sketch's step
`(nEW)^{O(1)} · e^{−k^{1/c}/c₀}` with `k = Θ(log^c(nκEW/δ))` (p.20) needs `log(nW)` to be `O(log(nκEW/δ))`,
which fails when `κ` is tiny and `W` huge, and the printed bound is then false with such a constant:
for `c = 4`, `c₀ = 1`, take `σ(x) = p(Sigmoid(x/W))` for a monotone polynomial staircase `p` depending
on `n` and `W` huge, so `κW` stays bounded; a depth-two circuit with `O(n)` wires then computes parity with
separation `Ω(1/n)`, and the printed bound would give degree `O(√n log²n)`, below the `n/2` required
for parity. So the logarithm here is taken of `n · max(κ, 1) · E · W/δ`. For any fixed `κ > 0` this is
the printed `O(√E log^{c/2}(nκEW/δ))` with a constant depending also on `κ`; it covers `κ = 1/4`, the
only value the paper uses.

**Formalization Note.** The constant `Cst` of the `O(·)` depends only on `c` and `c₀`: it is chosen
before `σ`, `κ`, `n`, `W`, `E`, `δ`, the circuit and `f`. The logarithm is written `log(2 + …)`, which is
at least `log 2 > 0`, since the printed logarithm may be `≤ 0`, where an `O(·)` bound is meaningless.
`δ > 0` (the printed `log(…/δ)` needs it). Lipschitz is `|σ x − σ y| ≤ κ |x − y|` with `κ ≥ 0`;
"depth-two" is `depth ≤ 2` at the output gate (the output gate may read inputs directly, as in the
proof, p.20). Real exponents are `Real.rpow`. -/
theorem theorem_4_4 :
    ∀ c : ℝ, 0 < c → ∀ c₀ : ℝ, 1 ≤ c₀ → ∃ Cst : ℝ, 0 < Cst ∧
      ∀ (σ : ℝ → ℝ) (κ : ℝ), (∀ x, σ x ∈ Set.Icc (0 : ℝ) 1) → Monotone σ → 0 ≤ κ →
        (∀ x y : ℝ, |σ x - σ y| ≤ κ * |x - y|) → RatApproxCond σ c c₀ →
        ∀ (n : ℕ) (W E δ : ℝ) (C : Circuit n) (f : (Fin n → Bool) → Bool),
          C.depth ≤ 2 → C.ParamsLe W → (C.wires : ℝ) ≤ E → 0 < δ → ComputesSep σ C f δ →
          SignRepBy f
            (Cst * Real.sqrt E * Real.log (2 + (n : ℝ) * max κ 1 * E * W / δ) ^ (c / 2)) := by sorry

end SigmoidWire
