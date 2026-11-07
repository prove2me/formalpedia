-- Prove2me | Theorems.Thm_QuadBogolyubov_lemma_D_5
-- name    : QuadBogolyubov.lemma_D_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:08:17.598768+00:00
-- url     : https://prove2.me/theorems/84bcf118-a04e-4b13-a37f-7bc27415df90
-- title:
--   Lemma D.5 — rank inheritance for block quadratic maps
-- statement:
--   Let $m\ge1$ and let $W$ be a quadratic variety as in (28). For $1\le i\le j\le m$ let $\lambda_{ij}\in\mathbb F_2^d$, not all zero. Then the bilinear form associated to
--   $$P(x_1,\dots,x_m)=\sum_{i=1}^mq_{\lambda_{ii}}(x_i)+\sum_{1\le i<j\le m}\beta_{\lambda_{ij}}(x_i,x_j)$$
--   on $G^m$ has rank at least $\mathrm{rk}(W)$. Consequently, for every linear form $L_0$ on $G^m$ and every $c\in\mathbb F_2$,
--   $$\Big|\mathbb E_{x_1,\dots,x_m\in G}(-1)^{P(x_1,\dots,x_m)+L_0(x_1,\dots,x_m)+c}\Big|\le2^{-\mathrm{rk}(W)/2}.$$
--   Here $q_\mu=\sum_k\mu_kq_k$ and $\beta_\mu=\sum_k\mu_k\beta_{q_k}$. This is used in every exponential-sum estimate of Appendix D.
--
--   Differences from the source:
--   - encoding: "as in (28)": complexity (0, d), containing 0, written W = {q = 0} with qⱼ(0) = 0 → `IsRooted W`: d₁ = 0, every bⱼ = 0, every qⱼ(0) = 0, with d = W.d2; reason: the normalization (28) itself, written as hypotheses
--   - encoding: rank at least rk(W); bound 2^{−rk(W)/2} → for every r with `HasRankAtLeast W r`: r ≤ rank of the form of P, and the bound 2^{−r/2}; reason: both bounds are monotone in r, so this is the statement at r = rk(W); for d₂ = 0 the hypothesis λ ≠ 0 cannot hold
--   - encoding: λ_{ij} for 1 ≤ i ≤ j ≤ m → lam : Fin m → Fin m → 𝔽₂ᵈ, of which only the entries with i ≤ j enter; reason: entries with i > j appear neither in P nor in the non-vanishing hypothesis
--   - reading: "λ₀ + λ₁q₁ + ⋯ + λ_{d₂}q_{d₂} is not a linear function for any (λ₀, …, λ_{d₂}) ≠ 0" (§3, p.9) → `QuadVariety.q_indep`: for every λ ≠ 0, Σλⱼqⱼ agrees on V with no polynomial of degree ≤ 1; reason: as printed the condition fails for λ = (1, 0, …, 0), so no variety would exist; the same sentence names the intent, "quadratic parts are linearly independent"
--   - encoding: qⱼ : V → F₂ quadratic functions on V → global quadratic polynomials on F₂ⁿ, used only on V; reason: p.68: each quadratic function on V extends to a quadratic polynomial on F₂ⁿ
--   - encoding: F₂ⁿ → Fin n → ZMod 2; reason: Lean convention; the same set
--   - encoding: (−1)^{P(x)+L₀(x)+c} with exponent in F₂ → `(-1 : ℝ) ^ (P x + L₀ x + c).val`; reason: the exponent is the value in {0, 1}; casting to ℝ would break 1 + 1 = 0
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Lemma D.5, p.54

import Mathlib
import Definitions.Def_QuadBogolyubov_IsRooted

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace QuadBogolyubov

/-- **Lemma D.5 (Rank inheritance for block quadratic maps).** Let `m ≥ 1` and let `W` be a
quadratic variety as in (28). For `1 ≤ i ≤ j ≤ m` let `λᵢⱼ ∈ 𝔽₂ᵈ`, not all zero. Then the bilinear
form of `P(x₁, …, x_m) = ∑ᵢ q_{λᵢᵢ}(xᵢ) + ∑_{i<j} β_{λᵢⱼ}(xᵢ, xⱼ)` on `Gᵐ` has rank at least
`rk(W)`, and consequently `|𝔼_{x∈Gᵐ}(−1)^{P(x)+L₀(x)+c}| ≤ 2^{−rk(W)/2}` for every linear form `L₀`
on `Gᵐ` and every `c ∈ 𝔽₂`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Lemma D.5, p.54: "Let m ≥ 1, and let W be a quadratic variety as in (28). For each
1 ≤ i ≤ j ≤ m, let λij ∈ F₂ᵈ, and suppose that at least one λij is non-zero. Then the bilinear form
assoicated to the quadratic function P(x1, . . . , xm) = Σ_{i=1}^m qλii(xi) +
Σ_{1≤i<j≤m} βλij(xi, xj) has rank at least rk(W). Consequently, for every linear form L0 on Gᵐ and
every c ∈ F2, |E_{x1,...,xm∈G}(−1)^{P(x1,...,xm)+L0(x1,...,xm)+c}| ≤ 2^{−rk(W)/2}."

**Formalization Note.** "as in (28)" is `IsRooted W`, `d = W.d2`, `G = 𝔽₂ⁿ`. The coefficients are
`lam : Fin m → Fin m → 𝔽₂ᵈ`, of which only the entries with `i ≤ j` enter; "at least one is
non-zero" ranges over those. `q_μ = ∑ₖ μₖ qₖ` and `β_μ = ∑ₖ μₖ β_{qₖ}` (App. D, p.53). The rank of
`W` enters through every `r` with `HasRankAtLeast W r`; the rank of a form on `Gᵐ` is `bilinRank`.
Both clauses are stated. -/
theorem lemma_D_5 {n : ℕ} (W : QuadVariety n) (hW : IsRooted W) (m : ℕ) (hm : 1 ≤ m)
    (lam : Fin m → Fin m → Fin W.d2 → ZMod 2) (hlam : ∃ i j, i ≤ j ∧ lam i j ≠ 0) :
    let qLam : (Fin W.d2 → ZMod 2) → (Fin n → ZMod 2) → ZMod 2 :=
      fun μ x => ∑ k, μ k * W.q k x
    let βLam : (Fin W.d2 → ZMod 2) → (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2 :=
      fun μ x y => ∑ k, μ k * bilin (W.q k) x y
    let P : (Fin m → Fin n → ZMod 2) → ZMod 2 :=
      fun x => ∑ i, qLam (lam i i) (x i) + ∑ i, ∑ j ∈ Finset.Ioi i, βLam (lam i j) (x i) (x j)
    ∀ r : ℝ, HasRankAtLeast W r →
      r ≤ (bilinRank (bilin P) : ℝ) ∧
      ∀ (L₀ : Module.Dual (ZMod 2) (Fin m → Fin n → ZMod 2)) (c : ZMod 2),
        |𝔼 x : Fin m → Fin n → ZMod 2, (-1 : ℝ) ^ (P x + L₀ x + c).val| ≤
          (2 : ℝ) ^ (-(r / 2)) := by sorry

end QuadBogolyubov
