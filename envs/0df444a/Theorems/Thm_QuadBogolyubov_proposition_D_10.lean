-- Prove2me | Theorems.Thm_QuadBogolyubov_proposition_D_10
-- name    : QuadBogolyubov.proposition_D_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:00:20.387207+00:00
-- url     : https://prove2.me/theorems/987037f9-a66c-40a9-939a-f2196ce1a3bb
-- title:
--   Proposition D.10 — weighted Gowers–Cauchy–Schwarz
-- statement:
--   Let $D_1,D_2,D_3\subseteq\mathbb F_2^n$ be non-empty, let $\rho_{12},\rho_{13},\rho_{23}$ be non-negative on $D_1\times D_2$, $D_1\times D_3$, $D_2\times D_3$, let $P,Q,R$ be 1-bounded on the same products and let $F:\mathbb F_2^n\to\mathbb C$ be 1-bounded. Put
--   $$\mathcal A(F)=\mathbb E_{a\in D_1,b\in D_2,c\in D_3}\rho_{12}(a,b)\rho_{13}(a,c)\rho_{23}(b,c)P(a,b)Q(a,c)R(b,c)F(a+b+c),$$
--   $$\mathcal B(F)=\mathbb E_{a_0,a_1\in D_1}\mathbb E_{b_0,b_1\in D_2}\mathbb E_{c_0,c_1\in D_3}\prod_{i,j}\rho_{12}(a_i,b_j)\prod_{i,k}\rho_{13}(a_i,c_k)\prod_{j,k}\rho_{23}(b_j,c_k)\prod_{i,j,k}\mathcal C^{i+j+k}F(a_i+b_j+c_k).$$
--   Then $\mathcal B(F)$ is non-negative and
--   $$|\mathcal A(F)|^8\le M_{12}^4M_{13}^2M_{23}\mathcal B(F),$$
--   where $M_{12}=\mathbb E_{a,b}\rho_{12}(a,b)$, $M_{13}=\mathbb E_{a,c_0,c_1}\rho_{13}(a,c_0)\rho_{13}(a,c_1)$ and $M_{23}=\mathbb E_{b_0,b_1,c_0,c_1}\prod_{i,j}\rho_{23}(b_i,c_j)$.
--
--   This is the Cauchy–Schwarz inequality behind the $U^3(W)$-control of $\Phi_W$.
--
--   Differences from the source:
--   - encoding: D₁, D₂, D₃ finite non-empty sets, with a + b + c ∈ G → non-empty `Finset`s of 𝔽₂ⁿ; reason: F(a + b + c) requires the sets to lie in G = F₂ⁿ
--   - encoding: ρ₁₂, ρ₁₃, ρ₂₃, P, Q, R functions on D_i × D_j → functions on G × G, constrained only on D_i × D_j; reason: only the values on D_i × D_j enter any average
--   - encoding: B(F) is non-negative → `0 ≤ ℬ` in the order of ℂ (real and ≥ 0), and the inequality uses ℬ.re; reason: the same statement
--   - encoding: F₂ⁿ → Fin n → ZMod 2; reason: Lean convention; the same set
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Proposition D.10, pp.57–58

import Mathlib

set_option autoImplicit false

open scoped BigOperators Pointwise
open scoped ComplexOrder

namespace QuadBogolyubov

/-- **Proposition D.10 (Weighted Gowers–Cauchy–Schwarz).** Let `D₁, D₂, D₃ ⊆ 𝔽₂ⁿ` be finite
non-empty sets, `ρ₁₂, ρ₁₃, ρ₂₃ ≥ 0` weights on `D₁ × D₂`, `D₁ × D₃`, `D₂ × D₃`, `P, Q, R` 1-bounded
complex functions on the same products and `F : 𝔽₂ⁿ → ℂ` 1-bounded. With `𝒜(F)`, `ℬ(F)`, `M₁₂`,
`M₁₃`, `M₂₃` as on the page, `ℬ(F)` is non-negative and `|𝒜(F)|⁸ ≤ M₁₂⁴ M₁₃² M₂₃ ℬ(F)`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Proposition D.10, pp.57–58: "Let D1, D2, D3 be finite non-empty sets. Let ρ12, ρ13, ρ23 be
non-negative functions on D1 × D2, D1 × D3, D2 × D3, respectively, and let P, Q, R be 1-bounded
functions on D1 × D2, D1 × D3, D2 × D3, respectively. Given a 1-bounded function F : G → C, define
A(F) = E_{a∈D1,b∈D2,c∈D3} ρ12(a, b)ρ13(a, c)ρ23(b, c)P(a, b)Q(a, c)R(b, c)F(a + b + c), and
B(F) = E_{a0,a1∈D1} E_{b0,b1∈D2} E_{c0,c1∈D3} ∏_{i,j∈{0,1}} ρ12(ai, bj) ∏_{i,k∈{0,1}} ρ13(ai, ck)
· ∏_{j,k∈{0,1}} ρ23(bj, ck) ∏_{i,j,k∈{0,1}} C^{i+j+k}F(ai + bj + ck). Then B(F) is non-negative and
|A(F)|⁸ ≤ M12⁴ M13² M23 B(F), where M12 = E_{a∈D1,b∈D2} ρ12(a, b),
M13 = E_{a∈D1,c0,c1∈D3} ρ13(a, c0)ρ13(a, c1), M23 = E_{b0,b1∈D2,c0,c1∈D3} ∏_{i,j∈{0,1}} ρ23(bi, cj)."

**Formalization Note.** `G = 𝔽₂ⁿ` (Appendix D); `D₁, D₂, D₃` are finite subsets of `G`, as
`F(a + b + c)` requires. The weights and the functions `P, Q, R` are functions on `G × G`, of which
only the values on `Dᵢ × Dⱼ` enter and are constrained. Pairs `(a₀, a₁)` are `a : Fin 2 → G`
averaged over `D₁²`; `𝒞^{i+j+k}` is complex conjugation applied `i + j + k` times.
"`ℬ(F)` is non-negative" is `0 ≤ ℬ(F)` in the order of `ℂ` (real and `≥ 0`). -/
theorem proposition_D_10 {n : ℕ} (D₁ D₂ D₃ : Finset (Fin n → ZMod 2))
    (h₁ : D₁.Nonempty) (h₂ : D₂.Nonempty) (h₃ : D₃.Nonempty)
    (ρ₁₂ ρ₁₃ ρ₂₃ : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ℝ)
    (hρ₁₂ : ∀ a ∈ D₁, ∀ b ∈ D₂, 0 ≤ ρ₁₂ a b) (hρ₁₃ : ∀ a ∈ D₁, ∀ c ∈ D₃, 0 ≤ ρ₁₃ a c)
    (hρ₂₃ : ∀ b ∈ D₂, ∀ c ∈ D₃, 0 ≤ ρ₂₃ b c)
    (P Q R : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ℂ)
    (hP : ∀ a ∈ D₁, ∀ b ∈ D₂, ‖P a b‖ ≤ 1) (hQ : ∀ a ∈ D₁, ∀ c ∈ D₃, ‖Q a c‖ ≤ 1)
    (hR : ∀ b ∈ D₂, ∀ c ∈ D₃, ‖R b c‖ ≤ 1)
    (F : (Fin n → ZMod 2) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) :
    let 𝒜 : ℂ := 𝔼 a ∈ D₁, 𝔼 b ∈ D₂, 𝔼 c ∈ D₃,
      ((ρ₁₂ a b * ρ₁₃ a c * ρ₂₃ b c : ℝ) : ℂ) * P a b * Q a c * R b c * F (a + b + c)
    let ℬ : ℂ := 𝔼 a ∈ Fintype.piFinset (fun _ : Fin 2 => D₁),
      𝔼 b ∈ Fintype.piFinset (fun _ : Fin 2 => D₂), 𝔼 c ∈ Fintype.piFinset (fun _ : Fin 2 => D₃),
        (((∏ i : Fin 2, ∏ j : Fin 2, ρ₁₂ (a i) (b j)) * (∏ i : Fin 2, ∏ k : Fin 2, ρ₁₃ (a i) (c k)) *
            (∏ j : Fin 2, ∏ k : Fin 2, ρ₂₃ (b j) (c k)) : ℝ) : ℂ) *
          ∏ i : Fin 2, ∏ j : Fin 2, ∏ k : Fin 2,
            (starRingEnd ℂ)^[i.val + j.val + k.val] (F (a i + b j + c k))
    let M₁₂ : ℝ := 𝔼 a ∈ D₁, 𝔼 b ∈ D₂, ρ₁₂ a b
    let M₁₃ : ℝ := 𝔼 a ∈ D₁, 𝔼 c₀ ∈ D₃, 𝔼 c₁ ∈ D₃, ρ₁₃ a c₀ * ρ₁₃ a c₁
    let M₂₃ : ℝ := 𝔼 b ∈ Fintype.piFinset (fun _ : Fin 2 => D₂),
      𝔼 c ∈ Fintype.piFinset (fun _ : Fin 2 => D₃), ∏ i : Fin 2, ∏ j : Fin 2, ρ₂₃ (b i) (c j)
    0 ≤ ℬ ∧ ‖𝒜‖ ^ 8 ≤ M₁₂ ^ 4 * M₁₃ ^ 2 * M₂₃ * ℬ.re := by sorry

end QuadBogolyubov
