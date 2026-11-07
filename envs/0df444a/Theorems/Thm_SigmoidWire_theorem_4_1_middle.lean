-- Prove2me | Theorems.Thm_SigmoidWire_theorem_4_1_middle
-- name    : SigmoidWire.theorem_4_1_middle
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:19.177321+00:00
-- url     : https://prove2.me/theorems/16365f9b-7d79-41b0-8e07-b7504b971c4e
-- title:
--   Proof of Theorem 4.1: the middle layer, $|V_k-\mathrm I[|x|\ge k]|\le 1/(10n)$
-- statement:
--   Let $n\ge1$, $1\le k\le n$ and $0\le m\le n$. Put $\gamma=1/6$, $A=\lceil(2n/\gamma)\ln(10n)\rceil$, $\tau_k=\mathrm{Sigmoid}((k-\tfrac12)/n)$ and
--
--   $$
--   V=\mathrm{Sigmoid}\bigl(A(\mathrm{Sigmoid}(m/n)-\tau_k)\bigr),
--   $$
--
--   which is the value of the gate $V_k$ on inputs of Hamming weight $m$. Then:
--
--   1. if $m\ge k$, then $\mathrm{Sigmoid}(m/n)-\tau_k\ge\mathrm{Sigmoid}(k/n)-\tau_k\ge\gamma/(2n)$ and $V\ge\mathrm{Sigmoid}(\ln(10n))$;
--   2. if $m<k$, then $V\le\mathrm{Sigmoid}(-\ln(10n))$;
--   3. $\mathrm{Sigmoid}(\ln(10n))=1-\frac1{10n+1}\ge1-\frac1{10n}$ and $\mathrm{Sigmoid}(-\ln(10n))\le\frac1{10n}$;
--   4. consequently
--
--   $$
--   \bigl|V-\mathrm I[m\ge k]\bigr|\le\frac1{10n}.
--   $$
--
--   So the $n$ gates $V_1,\dots,V_n$ of fan-in one approximate the threshold functions of the Hamming weight.
--
--   Differences from the source:
--   - encoding: Vk(x) with Sigmoid_sum(x) = Sigmoid(|x|/n) → the value at m = |x|, for every m ≤ n; reason: the gate depends on x only through |x|
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), proof of Theorem 4.1, p.18

import Mathlib

namespace SigmoidWire

/-- **Proof of Theorem 4.1, the middle layer: `|V_k(x) − I[|x| ≥ k]| ≤ 1/(10n)`.**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), proof of Theorem 4.1, p.18
(PDF p.20). With `γ = 1/6`, `Sigmoid_sum(x) = Sigmoid(|x|/n)`, `A := ⌈(2n/γ) ln(10n)⌉`,
`τ_k := Sigmoid((k − 1/2)/n)` and `V_k(x) := Sigmoid(A · (Sigmoid_sum(x) − τ_k))`: if `|x| ≥ k` then
`Sigmoid_sum(x) − τ_k ≥ Sigmoid(k/n) − Sigmoid((k − 1/2)/n) ≥ γ/(2n)` and
`V_k(x) ≥ Sigmoid(ln(10n)) = 1 − 1/(10n+1) ≥ 1 − 1/(10n)`; otherwise `V_k(x) ≤ Sigmoid(−ln(10n)) ≤ 1/(10n)`.

**Formalization Note.** `V_k(x)` depends on `x` only through `m = |x|`, so the statement is made
for every `m ∈ {0, …, n}`; `I[m ≥ k]` is `if k ≤ m then 1 else 0`; `ln` is `Real.log`; `⌈·⌉` is
`Int.ceil`. -/
theorem theorem_4_1_middle (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (m : ℕ) (hmn : m ≤ n) :
    let γ : ℝ := 1 / 6
    let A : ℝ := (⌈(2 * (n : ℝ) / γ) * Real.log (10 * n)⌉ : ℤ)
    let τ : ℝ := Real.sigmoid (((k : ℝ) - 1 / 2) / n)
    let V : ℝ := Real.sigmoid (A * (Real.sigmoid ((m : ℝ) / n) - τ))
    (k ≤ m → γ / (2 * n) ≤ Real.sigmoid ((k : ℝ) / n) - τ ∧
      Real.sigmoid ((k : ℝ) / n) - τ ≤ Real.sigmoid ((m : ℝ) / n) - τ ∧
      Real.sigmoid (Real.log (10 * n)) ≤ V) ∧
    (m < k → V ≤ Real.sigmoid (-Real.log (10 * n))) ∧
    Real.sigmoid (Real.log (10 * n)) = 1 - 1 / (10 * (n : ℝ) + 1) ∧
    1 - 1 / (10 * (n : ℝ) + 1) ≥ 1 - 1 / (10 * (n : ℝ)) ∧
    Real.sigmoid (-Real.log (10 * n)) ≤ 1 / (10 * (n : ℝ)) ∧
    |V - (if k ≤ m then 1 else 0)| ≤ 1 / (10 * (n : ℝ)) := by sorry

end SigmoidWire
