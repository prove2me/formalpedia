-- Prove2me | Theorems.Thm_SigmoidWire_theorem_4_1_output
-- name    : SigmoidWire.theorem_4_1_output
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:19.41557+00:00
-- url     : https://prove2.me/theorems/79061a00-f40b-46fc-bbff-796d06941985
-- title:
--   Proof of Theorem 4.1: the output gate, $|L-F(m)|\le 1/10$ and the separation
-- statement:
--   Let $n\ge1$, $F:\mathbb N\to\{0,1\}$, $m\le n$, and let $V_1,\dots,V_n$ be reals with $|V_k-\mathrm I[m\ge k]|\le 1/(10n)$. Put $c_k=F(k)-F(k-1)$ and $L=F(0)+\sum_{k=1}^n c_kV_k$. Then:
--
--   1. $F(m)=F(0)+\sum_{k=1}^n c_k\,\mathrm I[m\ge k]$, with $c_k\in\{-1,0,1\}$ and $\sum_k|c_k|\le n$;
--   2. $|L-F(m)|\le 1/10$;
--   3. if $F(m)=1$, then $L\ge 9/10$ and $\mathrm{Sigmoid}(4(L-\tfrac12))\ge\mathrm{Sigmoid}(8/5)>3/4$;
--   4. if $F(m)=0$, then $L\le 1/10$ and $\mathrm{Sigmoid}(4(L-\tfrac12))\le\mathrm{Sigmoid}(-8/5)<1/2$.
--
--   This is the numerical core of the separation $1/4$ of the depth-three circuit.
--
--   Differences from the source:
--   - generalization: the circuit's gates Vk(x) → any reals V₁, …, Vₙ with the bound |Vₖ − I[m ≥ k]| ≤ 1/(10n); reason: the gates satisfy this bound (previous step), so this specializes to the source
--   - encoding: F : {0, 1, . . . , n} → {0, 1}, m = |x| → F : ℕ → Bool, m ≤ n; reason: only the values on {0, …, n} are used
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), proof of Theorem 4.1, pp.18–19

import Mathlib

namespace SigmoidWire

/-- **Proof of Theorem 4.1, the output gate.**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), proof of Theorem 4.1,
pp.18–19 (PDF pp.20–21): "F(m) = F(0) + Σ_{k=1}^n c_k I[m ≥ k] with c_k := F(k) − F(k − 1) ∈ {−1, 0, 1}";
with `L(x) := F(0) + Σ_k c_k V_k(x)` and `Σ_k |c_k| ≤ n`, `|L(x) − F(|x|)| ≤ n · 1/(10n) = 1/10`; and
the output `C(x) := Sigmoid(4(L(x) − 1/2))` satisfies: if `f(x) = 1` then `L(x) ≥ 9/10` and
`C(x) ≥ Sigmoid(8/5) > 3/4`; if `f(x) = 0` then `L(x) ≤ 1/10` and `C(x) ≤ Sigmoid(−8/5) < 1/2`.

**Formalization Note.** The statement is the real-number core of the output-gate step: `F` is any
map `ℕ → {0,1}` (only its values on `{0, …, n}` matter), `m = |x| ≤ n`, and `V_1, …, V_n` are any
reals with `|V_k − I[m ≥ k]| ≤ 1/(10n)` (the conclusion of the middle-layer step). `F(m) = 1` is
`F m = true`; `I[m ≥ k]` is `if k ≤ m then 1 else 0`. -/
theorem theorem_4_1_output (n : ℕ) (hn : 1 ≤ n) (F : ℕ → Bool) (m : ℕ) (hmn : m ≤ n)
    (V : ℕ → ℝ)
    (hV : ∀ k ∈ Finset.Icc 1 n, |V k - (if k ≤ m then 1 else 0)| ≤ 1 / (10 * (n : ℝ))) :
    let b : ℕ → ℝ := fun j => if F j then 1 else 0
    let c : ℕ → ℝ := fun k => b k - b (k - 1)
    let L : ℝ := b 0 + ∑ k ∈ Finset.Icc 1 n, c k * V k
    b m = b 0 + ∑ k ∈ Finset.Icc 1 n, c k * (if k ≤ m then 1 else 0) ∧
    (∀ k ∈ Finset.Icc 1 n, c k = -1 ∨ c k = 0 ∨ c k = 1) ∧
    ∑ k ∈ Finset.Icc 1 n, |c k| ≤ n ∧
    |L - b m| ≤ 1 / 10 ∧
    (F m = true → 9 / 10 ≤ L ∧ Real.sigmoid (8 / 5) ≤ Real.sigmoid (4 * (L - 1 / 2)) ∧
      3 / 4 < Real.sigmoid (8 / 5)) ∧
    (F m = false → L ≤ 1 / 10 ∧ Real.sigmoid (4 * (L - 1 / 2)) ≤ Real.sigmoid (-(8 / 5)) ∧
      Real.sigmoid (-(8 / 5)) < 1 / 2) := by sorry

end SigmoidWire
