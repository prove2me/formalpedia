-- Prove2me | Theorems.Thm_RegimeDRCVaR_tractable_m1_m2
-- name    : RegimeDRCVaR.tractable_m1_m2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:23:30.325474+00:00
-- url     : https://prove2.me/theorems/b29f2709-2f0d-4d7f-a9ee-036563689908
-- title:
--   Proof of Theorem 1 — the norm constraint is linear for $m=1$ and a second-order cone for $m=2$ (corrected: $\Omega_{soc}$ is the second-order cone $\|b\|_2\le a$)
-- statement:
--   Let $x\in\mathbb R^I$ and $\beta\in\mathbb R$.
--
--   1. For $m=1$ (so $m^*=\infty$) and $I\ge1$ assets: $\beta\ge\|x\|_{m^*}$ iff $\beta\ge x_i$ and $\beta\ge-x_i$ for every $i\in[I]$.
--   2. For $m=2$ (so $m^*=2$): $\beta\ge\|x\|_{m^*}$ iff $(\beta,x)\in\Omega_{soc}$, the second-order cone $\{(a,b)\mid\|b\|_2\le a\}$.
--
--   These are the forms in which (12) is a linear program ($m=1$) and a second-order cone program ($m=2$).
--
--   **Formalization Note** The cone is the published `PolyhedralSOC.Shared.LorentzCone I` $=\{(y,t)\mid\sqrt{\sum_i y_i^2}\le t\}$, with the pair written $(x,\beta)$.
--
--   Differences from the source:
--   - correction: p.4: (a,b) ∈ Ω_soc means ‖b‖₂² ≤ a² → (x, β) ∈ PolyhedralSOC.Shared.LorentzCone I, i.e. ‖x‖₂ ≤ β; reason: the printed set is a double cone and the m = 2 equivalence is false: (β, x) = (−1, 0) satisfies ‖0‖₂² ≤ (−1)² but not β ≥ ‖0‖₂ = 0; the second-order cone is the standard meaning of 'second-order conic constraint'
--   - encoding: ℓm norm ‖·‖_m and conjugate norm ‖·‖_{m*} on ℝ^I → normM m (the PiLp m norm on Fin I → ℝ) and normM (ENNReal.conjExponent m); reason: Lean convention; ENNReal.conjExponent sends 1 ↦ ∞, 2 ↦ 2, ∞ ↦ 1, the Hölder conjugate
--   - encoding: the pair (β, x) → the pair (x, β); reason: argument order of the published LorentzCone; same set
--   - reading: a market with I risky assets, i ∈ [I] (p.9) → the m = 1 clause assumes 0 < I; reason: the source has I ≥ 1 assets (its budget 1′x = 1 needs one); for I = 0, ‖x‖_∞ = 0 and the system β ≥ ±x_i is empty, so the equivalence would fail at β = −1; no other clause carries the hypothesis
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, proof of Theorem 1, p.ec3 (end of the proof); Ω_soc, Notation, p.4

import Mathlib
import Definitions.Def_RegimeDRCVaR_normM
import Definitions.Def_PolyhedralSOC_Shared_LorentzCone

open scoped ENNReal

namespace RegimeDRCVaR

/-- **Tractable forms for m = 1 and m = 2** (Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930,
proof of Theorem 1, p.ec3), with `Ω_soc` corrected to the second-order cone: "When m = 1, the
second set of constraints in (12) is equivalent to: β ≥ x_i, ∀i ∈ [I], β ≥ −x_i, ∀i ∈ [I]. When
m = 2, the second set of constraints in (12) is equivalent to: (β, x) ∈ Ω_soc."
1. For `m = 1` and `I ≥ 1` assets: `β ≥ ‖x‖_{1*}` iff `β ≥ x_i` and `β ≥ −x_i` for every `i ∈ [I]`.
2. For `m = 2`: `β ≥ ‖x‖_{2*}` iff `(β, x)` lies in the second-order cone `‖x‖₂ ≤ β`.

**Formalization Note**
* Correction: p.4 defines `(a, b) ∈ Ω_soc` as `‖b‖₂² ≤ a²`, a double cone; `(β, x) = (−1, 0)`
  satisfies `‖0‖₂² ≤ (−1)²` but not `β ≥ ‖0‖₂`, so the `m = 2` equivalence is false as printed.
  `Ω_soc` is read as the second-order cone `‖b‖₂ ≤ a`, the published
  `PolyhedralSOC.Shared.LorentzCone I = {(y, t) | √(∑ yᵢ²) ≤ t}`, with the pair written `(x, β)`.
* The `m = 1` clause assumes `0 < I` (p.9: "a market with I risky assets"; the budget
  `1′x = 1` needs `I ≥ 1`): for `I = 0`, `‖x‖_∞ = 0` and the system `β ≥ ±x_i` is empty, so the
  equivalence would fail at `β = −1`.
* `‖x‖_{m*}` is `normM (ENNReal.conjExponent m) x`; `ENNReal.conjExponent 1 = ∞` and
  `ENNReal.conjExponent 2 = 2`. -/
theorem tractable_m1_m2 {I : ℕ} :
    (0 < I → ∀ (x : Fin I → ℝ) (β : ℝ),
      β ≥ normM (ENNReal.conjExponent 1) x ↔ ∀ i, β ≥ x i ∧ β ≥ -x i) ∧
    (∀ (x : Fin I → ℝ) (β : ℝ),
      β ≥ normM (ENNReal.conjExponent 2) x ↔ (x, β) ∈ PolyhedralSOC.Shared.LorentzCone I) := by sorry

end RegimeDRCVaR
