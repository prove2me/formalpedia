-- Prove2me | Theorems.Thm_SinkhornHall_step2_output_hall_blocker
-- name    : SinkhornHall.step2_output_hall_blocker
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:47.130986+00:00
-- url     : https://prove2.me/theorems/b59cc105-7897-4f5c-80c3-1037a2c509b1
-- title:
--   Proof of Theorem 4.1 — rounding: on a certificate, every step-2 output $X$ has $\Gamma(X)\subseteq\{j_1,\dots,j_{k^*-1}\}$
-- statement:
--   Let $A$ be a nonnegative $n\times n$ matrix with no zero row or column, and let $x,y$ be positive vectors with
--
--   $$x_iy_j\ <\ (x_1\cdots x_n\,y_1\cdots y_n)^{1/n}\qquad\text{for every edge } ij \ (A_{ij}>0).$$
--
--   Sort $x_{i_1}\ge\dots\ge x_{i_n}$ and $y_{j_1}\le\dots\le y_{j_n}$ (any tie-break) and let $k^*$ satisfy $(x_{i_{k^*}}y_{j_{k^*}})^n\ge x_1\cdots x_ny_1\cdots y_n$. Then
--
--   $$\Gamma(\{i_1,\dots,i_{k^*}\})\ \subseteq\ \{j_1,\dots,j_{k^*-1}\},$$
--
--   and in particular $\{i_1,\dots,i_{k^*}\}$ is a Hall blocker: $|\Gamma(X)|<|X|$.
--
--   This is the rounding step that turns the analytic certificate into a combinatorial one.
--
--   **Formalization Note** Indices are 0-based: $i_t=\sigma(t-1)$, $j_t=\tau(t-1)$, and $k=k^*-1$, so the output is $\sigma(\{0,\dots,k\})$ and the bound is $\tau(\{0,\dots,k-1\})$.
--
--   Differences from the source:
--   - reading: §4 standing assumptions (p.15): G = G(A) for a nonnegative n × n matrix A, no isolated node, n = |U| = |V|, (r, c) = (1, 1) → A : Matrix (Fin n) (Fin n) ℝ with hA, hrow, hcol, and marginals 1; reason: stated once at the top of §4 and in force for Theorem 4.1 and its proof
--   - reading: x_iy_j < (x_1⋯x_ny_1⋯y_n)^{1/n}, obtained in the proof from Corollary 2.6 → the same inequality as hypothesis hedge; reason: this step of the proof uses only that inequality and the step-2 choices
--   - reading: the sorts and k* chosen in step 2 (ties unspecified) → every σ, τ, k with x ∘ σ antitone, y ∘ τ monotone and the k* inequality; reason: the argument applies to every admissible choice
--   - encoding: 1-based indices i_1, …, i_n and k* ∈ {1, …, n} → Fin n (0-based), i_t = σ (t − 1), k = k* − 1, output σ '' {0, …, k}; reason: Lean convention; the output has k* elements as in the paper
--   - encoding: (·)^{1/n} → Real.rpow with exponent 1/n; reason: the base is positive
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, proof of Theorem 4.1, p.16 ('By Corollary 2.6, it holds x_iy_j < (x_1⋯x_ny_1⋯y_n)^{1/n} for each edge ij in G. … is a Hall blocker.')

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset

namespace SinkhornHall

/-- **Rounding: on a certificate, every step-2 output is a Hall blocker.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, proof of Theorem 4.1, p.16: "By Corollary 2.6, it holds
x_i y_j < (x₁⋯xₙy₁⋯yₙ)^{1/n} for each edge ij in G. Therefore, G has no edge between i_k and j_ℓ for
k ≤ k*, ℓ ≥ k*, since x_{i_k} y_{j_ℓ} ≥ x_{i_{k*}} y_{j_{k*}} ≥ (x₁⋯xₙy₁⋯yₙ)^{1/n}. Thus
Γ({i₁, i₂, …, i_{k*}}) ⊆ {j₁, j₂, …, j_{k*−1}}. That is, the output {i₁, i₂, …, i_{k*}} is a Hall
blocker."

Setting of §4 (p.15): `A` nonnegative `n × n` with no zero row or column. For positive `x`, `y`
with `x_i y_j < (∏x ∏y)^{1/n}` on every edge, and every admissible choice in step 2 (sorting
permutations `σ`, `τ` and index `k`), the output `X = σ '' {0, …, k}` satisfies
`Γ(X) ⊆ τ '' {0, …, k − 1}` and `|Γ(X)| < |X|`.

**Formalization Note.** 0-based indices: `i_t = σ (t − 1)`, `j_t = τ (t − 1)`, `k = k* − 1`. The
power `1/n` is `Real.rpow` on the positive number `∏x ∏y`. -/
theorem step2_output_hall_blocker {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j)
    (x y : Fin n → ℝ) (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 < y j)
    (hedge : ∀ i j, 0 < A i j → x i * y j < ((∏ i', x i') * ∏ j', y j') ^ ((1 : ℝ) / n))
    (σ τ : Equiv.Perm (Fin n)) (k : Fin n) (hσ : Antitone (x ∘ σ)) (hτ : Monotone (y ∘ τ))
    (hk : (∏ i, x i) * (∏ j, y j) ≤ (x (σ k) * y (τ k)) ^ n) :
    Gamma A ((Finset.univ.filter (fun t : Fin n => t ≤ k)).image σ) ⊆
        (Finset.univ.filter (fun t : Fin n => t < k)).image τ ∧
      IsHallBlocker A ((Finset.univ.filter (fun t : Fin n => t ≤ k)).image σ) := by sorry

end SinkhornHall
