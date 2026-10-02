-- Prove2me | Theorems.Thm_Transcendence_exists_exp_monomials_small_on_grid
-- name    : Transcendence.exists_exp_monomials_small_on_grid
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:17:53.965345+00:00
-- url     : https://prove2.me/theorems/f435be21-31ad-48d9-a07d-c81bc63cb88c
-- title:
--   An integer combination of exponential monomials with small derivatives at the lattice points (4.16), and its growth
-- statement:
--   Let $\iota$ be a finite set, $n = |\iota|$, $k_0 \in \iota$, $d_0 \le 1$ and $d = d_0 + d_1$, and let $x_1, \dots, x_{d_1}$ and $y_j$ ($j \in \iota$) be vectors in $\mathbb{C}^\iota$ with $\sum_{i,\nu}|x_{i\nu}| \le c_x$ and $\sum_j\|y_j\| \le c_y$, where $\|\cdot\|$ is the sup norm. Let $S_1, T \ge 1$ be integers, $U, N > 0$ and $E$ real numbers, and put $r = (c_y + 2)S_1$ and $R = Er$. Assume
--
--   $$12n^2 \le N + 2U, \qquad e \le E \le e^{(N + 2U)/6}, \qquad (T+1)^{d}R^{T}e^{c_xTR} \le e^{U}, \qquad \bigl(2(N + 2U)\bigr)^{n+1} \le (T+1)^{d}N(\log E)^{n}.$$
--
--   Then there are integers $p_{\tau,t}$ ($0 \le \tau \le d_0T$, $t \in \{0, \dots, T\}^{d_1}$), not all zero, with $|p_{\tau,t}| \le e^{N}$, such that the function
--
--   $$F(z) = \sum_{\tau, t} p_{\tau,t}\, z_{k_0}^{\tau}\, e^{\langle t_1x_1 + \dots + t_{d_1}x_{d_1},\, z\rangle}, \qquad \langle w, z\rangle = \sum_\nu w_\nu z_\nu,$$
--
--   satisfies:
--
--   - at every point $\sum_j s_jy_j$ with $0 \le s_j < S_1$, every derivative of $F$ along a list of $k$ coordinate directions has modulus at most $k!\,e^{-U}$;
--   - $|F(w)| \le (T+1)^{d}e^{N}\rho^{T}e^{c_xT\rho}$ whenever $\rho \ge 1$ and $\|w\| \le \rho$.
--
--   The assumptions are those of Proposition 4.10 (`Transcendence.siegel_small_values`) for these $(T+1)^d$ monomials, with $V = U$ and the radii $r$ and $R$. The first conclusion is (4.16), and the second is the growth bound that the Schwarz step of `Transcendence.schneider_lang_cartesian` needs.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None: step 3 of §4.6 of Waldschmidt's book and (4.16) (pp. 138–139), with $V = U$ and the book's radii $r = c_2S_1$, $R = Er$, where $c_y + 2$ replaces $c_2 = |y_1| + \dots + |y_n| + 2$. The bound has $k!$ in place of the book's $\sigma!$, which is at most $k!$. The contribution of this node is the formal proof.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, §4.6, step 3 and (4.16) (pp. 138–139). Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- **An auxiliary function that is small on the grid** (Waldschmidt, *Diophantine Approximation on Linear
Algebraic Groups*, §4.6, step 3 and (4.16)). Let `n = |ι|`, `d₀ ≤ 1`, `d = d₀ + d₁`, `cx ≥ Σ_{i,ν} |x_{iν}|` and
`cy ≥ Σ_j ‖y_j‖`, and let `S₁, T ≥ 1`, `U, N > 0` and `E` satisfy the conditions of Prop. 4.10 for the radii
`r = (cy + 2) S₁` and `R = E r`: `12n² ≤ N + 2U`, `e ≤ E ≤ e^{(N + 2U)/6}`,
`(T+1)^d R^T e^{cx T R} ≤ e^U` and `(2(N + 2U))^{n+1} ≤ (T+1)^d N (log E)ⁿ`. Then there are integers `p_{τ,t}`
(`0 ≤ τ ≤ d₀T`, `t ∈ {0, …, T}^{d₁}`), not all zero, with `|p_{τ,t}| ≤ e^N`, such that the function
`F(z) = Σ p_{τ,t} · z_{k₀}^τ · exp ⟨t₁x₁ + ⋯ + t_{d₁}x_{d₁}, z⟩` has every mixed partial derivative of order `k`
at every lattice point `Σ_j s_j y_j` (`0 ≤ s_j < S₁`) bounded by `k! e^{-U}`, and
`|F(w)| ≤ (T+1)^d e^N ρ^T e^{cx T ρ}` whenever `‖w‖ ≤ ρ` and `ρ ≥ 1`. -/
theorem exists_exp_monomials_small_on_grid {ι : Type*} [Fintype ι] [DecidableEq ι] {d₁ : ℕ}
    (x : Fin d₁ → ι → ℂ) (y : ι → ι → ℂ) (k₀ : ι) {d₀ : ℕ} (hd₀ : d₀ ≤ 1) {cx cy : ℝ}
    (hcx : ∑ i, ∑ ν, ‖x i ν‖ ≤ cx) (hcy : ∑ j, ‖y j‖ ≤ cy) {S₁ T : ℕ} {E U N : ℝ}
    (hS₁ : 1 ≤ S₁) (hT : 1 ≤ T) (hU : 0 < U) (hN : 0 < N)
    (hSL : 12 * (Fintype.card ι : ℝ) ^ 2 ≤ N + U + U ∧ Real.exp 1 ≤ E ∧
      E ≤ Real.exp ((N + U + U) / 6) ∧
      ((T : ℝ) + 1) ^ (d₀ + d₁) * (E * ((cy + 2) * S₁)) ^ T *
        Real.exp (cx * T * (E * ((cy + 2) * S₁))) ≤ Real.exp U ∧
      (2 * (N + U + U)) ^ (Fintype.card ι + 1) ≤
        ((T : ℝ) + 1) ^ (d₀ + d₁) * N * Real.log E ^ Fintype.card ι) :
    ∃ p : Fin (d₀ * T + 1) × (Fin d₁ → Fin (T + 1)) → ℤ, p ≠ 0 ∧
      (∀ l, |(p l : ℝ)| ≤ Real.exp N) ∧
      (∀ (s : ι → Fin S₁) (k : ℕ) (L : Fin k → ι),
        ‖iteratedFDeriv ℂ k (fun z : ι → ℂ => ∑ l, (p l : ℂ) * (z k₀ ^ (l.1 : ℕ) *
          Complex.exp (∑ ν, (∑ i, ((l.2 i : ℕ) : ℂ) * x i ν) * z ν))) (∑ j, ((s j : ℕ) : ℂ) • y j)
          (fun l => Pi.single (L l) 1)‖ ≤ k.factorial * Real.exp (-U)) ∧
      ∀ ρ : ℝ, 1 ≤ ρ → ∀ w : ι → ℂ, ‖w‖ ≤ ρ →
        ‖∑ l, (p l : ℂ) * (w k₀ ^ (l.1 : ℕ) *
          Complex.exp (∑ ν, (∑ i, ((l.2 i : ℕ) : ℂ) * x i ν) * w ν))‖ ≤
          ((T : ℝ) + 1) ^ (d₀ + d₁) * Real.exp N * ρ ^ T * Real.exp (cx * T * ρ) := by
  sorry

end Transcendence
