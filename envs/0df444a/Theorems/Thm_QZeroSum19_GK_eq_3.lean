-- Prove2me | Theorems.Thm_QZeroSum19_GK_eq_3
-- name    : QZeroSum19.GK.eq_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:15.83937+00:00
-- url     : https://prove2.me/theorems/e6dcff67-73d8-4583-8ab2-ac5c433cfea2
-- title:
--   Proof of Lemma 1, p. 5, (3) — with probability ≥ 1 − δ′, every gap is ≤ (ln(nm/δ′) + 3Σ_τ η(τ)²)/Σ_τ η(τ)
-- statement:
--   Let $n,m\ge1$, $A\in[-1,1]^{n\times m}$, and let $\eta(1),\eta(2),\dots$ be step sizes with $0<\eta(\tau)\le1/2$ for every $\tau\ge1$. Fix $\delta'>0$ and $t\ge1$, run Algorithm 1 for $t$ iterations, and let $\bar x=x_t/\|x_t\|_1$, $\bar y=y_t/\|y_t\|_1$ be the normalized iterates. Then, with probability at least $1-\delta'$,
--   $$(A\bar y)_i-(A^{\mathsf T}\bar x)_j\ \le\ \frac{\ln\!\big(nm/\delta'\big)+3\sum_{\tau=1}^{t}\eta(\tau)^2}{\sum_{\tau=1}^{t}\eta(\tau)}\qquad\text{for all } i\in[n],\ j\in[m].\tag{3}$$
--
--   This is display (3) of the paper, the high-probability gap bound valid for every step schedule; both versions of Lemma 1 follow from it by choosing $\eta$ and $\delta'$.
--
--   **Formalization Note** $\delta'$ stands for the page's $\delta^{(t)}$. The normalization divides by $\sum_k (x_t)_k=\sum_{\tau=1}^t\eta(\tau)=\|x_t\|_1$ (the iterates are nonnegative). Steps are required to be positive only for $\tau\ge1$; the value at $\tau=0$ is never used.
-- source:
--   van Apeldoorn and Gilyén, Quantum algorithms for zero-sum games, arXiv:1904.03180v1, p. 5, proof of Lemma 1, (3)

import Mathlib
import Definitions.Def_QZeroSum19_GK_Setting

open Matrix

namespace QZeroSum19.GK

/-- Proof of Lemma 1, p. 5, (3): for `δ' > 0` and `t ≥ 1` iterations with steps `η(τ) ∈ (0, 1/2]`,
with probability at least `1 − δ'`, every gap of the normalized iterates satisfies
`(Aȳ)_i − (Aᵀx̄)_j ≤ (ln(nm/δ') + 3 Σ_{τ=1}^{t} η(τ)²) / Σ_{τ=1}^{t} η(τ)`. -/
theorem eq_3 {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) (η : ℕ → ℝ) (hη : ∀ τ, 1 ≤ τ → 0 < η τ ∧ η τ ≤ 1 / 2)
    (δ' : ℝ) (hδ' : 0 < δ') (t : ℕ) (ht : 1 ≤ t) :
    1 - δ' ≤ prob A η t (fun ω => ∀ i j,
      (A *ᵥ normalize (yAfter η ω t)) i - (Aᵀ *ᵥ normalize (xAfter η ω t)) j ≤
        (Real.log ((n : ℝ) * m / δ') + 3 * ∑ τ ∈ Finset.Icc 1 t, η τ ^ 2) /
          ∑ τ ∈ Finset.Icc 1 t, η τ) := by sorry

end QZeroSum19.GK
