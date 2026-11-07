-- Prove2me | Theorems.Thm_QuadBogolyubov_lemma_D_7
-- name    : QuadBogolyubov.lemma_D_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:08:07.328901+00:00
-- url     : https://prove2.me/theorems/291327f1-6d23-410a-b75d-1cb19b80be03
-- title:
--   Lemma D.7 — characterising rooted Gowers cubes
-- statement:
--   Let $W$ be a quadratic variety as in (28) with bilinear variety $B$.
--
--   1. For $x_1,x_2,x_3\in G$: $x_1,x_2,x_3,x_1+x_2,x_1+x_3,x_2+x_3\in W$ if and only if $x_1,x_2,x_3\in W$ and $(x_1,x_2),(x_1,x_3),(x_2,x_3)\in B$.
--   2. Consequently,
--   $$\prod_{\epsilon\in\{0,1\}^3\setminus\{(0,0,0)\}}\mathbf 1_W(\epsilon_1x_1+\epsilon_2x_2+\epsilon_3x_3)=\prod_{i\in[3]}\mathbf 1_W(x_i)\prod_{i<j\in[3]}\mathbf 1_B(x_i,x_j).$$
--   3. If $x_0,x_1,y_0,y_1,z_0,z_1\in W$ and $(x_i,y_j),(x_i,z_k),(y_j,z_k)\in B$ for all $i,j,k\in\{0,1\}$, then $x_i+y_j+z_k\in W$ for all $i,j,k$.
--
--   This rewrites the cube count in terms of $W$ and $B$.
--
--   Differences from the source:
--   - encoding: "as in (28)": complexity (0, d), containing 0, written W = {q = 0} with qⱼ(0) = 0 → `IsRooted W`: d₁ = 0, every bⱼ = 0, every qⱼ(0) = 0, with d = W.d2; reason: the normalization (28) itself, written as hypotheses
--   - reading: "λ₀ + λ₁q₁ + ⋯ + λ_{d₂}q_{d₂} is not a linear function for any (λ₀, …, λ_{d₂}) ≠ 0" (§3, p.9) → `QuadVariety.q_indep`: for every λ ≠ 0, Σλⱼqⱼ agrees on V with no polynomial of degree ≤ 1; reason: as printed the condition fails for λ = (1, 0, …, 0), so no variety would exist; the same sentence names the intent, "quadratic parts are linearly independent"
--   - encoding: qⱼ : V → F₂ quadratic functions on V → global quadratic polynomials on F₂ⁿ, used only on V; reason: p.68: each quadratic function on V extends to a quadratic polynomial on F₂ⁿ
--   - encoding: x₀, x₁, y₀, y₁, z₀, z₁; the indicators → x y z : Fin 2 → G; the indicators are real-valued; reason: Lean convention
--   - encoding: F₂ⁿ → Fin n → ZMod 2; reason: Lean convention; the same set
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Lemma D.7, pp.54–55

import Mathlib
import Definitions.Def_QuadBogolyubov_IsRooted
import Definitions.Def_QuadBogolyubov_gowersU3

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace QuadBogolyubov

/-- **Lemma D.7 (Characterising rooted Gowers cubes).** Let `W` be a quadratic variety as in (28)
with bilinear variety `B`. (a) For `x₁, x₂, x₃ ∈ G`: `x₁, x₂, x₃, x₁+x₂, x₁+x₃, x₂+x₃ ∈ W` if and
only if `x₁, x₂, x₃ ∈ W` and `(x₁, x₂), (x₁, x₃), (x₂, x₃) ∈ B`. (b) Consequently
`∏_{ε∈{0,1}³\{0}} 1_W(ε₁x₁ + ε₂x₂ + ε₃x₃) = ∏_{i∈[3]} 1_W(xᵢ) ∏_{i<j} 1_B(xᵢ, xⱼ)`. (c) If
`x₀, x₁, y₀, y₁, z₀, z₁ ∈ W` and `(xᵢ, yⱼ), (xᵢ, z_k), (yⱼ, z_k) ∈ B` for all `i, j, k ∈ {0,1}`, then
`xᵢ + yⱼ + z_k ∈ W` for all `i, j, k`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Lemma D.7, pp.54–55: "Let W be a quadratic variety as in (28). For x1, x2, x3 ∈ G, the
following are equivalent. (1) x1, x2, x3, x1 + x2, x1 + x3, x2 + x3 ∈ W; (2) x1, x2, x3 ∈ W and
(x1, x2), (x1, x3), (x2, x3) ∈ B. Consequently, ∏_{ϵ∈{0,1}³\{(0,0,0)}} 1W(ϵ1x1 + ϵ2x2 + ϵ3x3) =
∏_{i∈[3]} 1W(xi) ∏_{i<j∈[3]} 1B(xi, xj). Moreover, if x0, x1, y0, y1, z0, z1 ∈ W and
(xi, yj), (xi, zk), (yj, zk) ∈ B for all i, j, k ∈ {0, 1}, then xi + yj + zk ∈ W for every
i, j, k ∈ {0, 1}."

**Formalization Note.** "as in (28)" is `IsRooted W`; `B` is `bilinVar W` of (29). The indicators
are real-valued. In (c) the pairs `(x₀, x₁)`, `(y₀, y₁)`, `(z₀, z₁)` are `x y z : Fin 2 → G`. All
three clauses are stated. -/
theorem lemma_D_7 {n : ℕ} (W : QuadVariety n) (hW : IsRooted W) :
    (∀ x₁ x₂ x₃ : Fin n → ZMod 2,
      (x₁ ∈ W.carrier ∧ x₂ ∈ W.carrier ∧ x₃ ∈ W.carrier ∧
          x₁ + x₂ ∈ W.carrier ∧ x₁ + x₃ ∈ W.carrier ∧ x₂ + x₃ ∈ W.carrier) ↔
        (x₁ ∈ W.carrier ∧ x₂ ∈ W.carrier ∧ x₃ ∈ W.carrier ∧
          (x₁, x₂) ∈ bilinVar W ∧ (x₁, x₃) ∈ bilinVar W ∧ (x₂, x₃) ∈ bilinVar W)) ∧
    (∀ x₁ x₂ x₃ : Fin n → ZMod 2,
      ∏ ε ∈ Finset.univ.filter (fun ε : Fin 3 → ZMod 2 => ε ≠ 0),
          (ind W.carrier (ε 0 • x₁ + ε 1 • x₂ + ε 2 • x₃) : ℝ) =
        ((ind W.carrier x₁ : ℝ) * ind W.carrier x₂ * ind W.carrier x₃) *
          ((ind (bilinVar W) (x₁, x₂) : ℝ) * ind (bilinVar W) (x₁, x₃) *
            ind (bilinVar W) (x₂, x₃))) ∧
    (∀ x y z : Fin 2 → (Fin n → ZMod 2),
      (∀ i, x i ∈ W.carrier) → (∀ j, y j ∈ W.carrier) → (∀ k, z k ∈ W.carrier) →
      (∀ i j, (x i, y j) ∈ bilinVar W) → (∀ i k, (x i, z k) ∈ bilinVar W) →
      (∀ j k, (y j, z k) ∈ bilinVar W) →
      ∀ i j k, x i + y j + z k ∈ W.carrier) := by sorry

end QuadBogolyubov
