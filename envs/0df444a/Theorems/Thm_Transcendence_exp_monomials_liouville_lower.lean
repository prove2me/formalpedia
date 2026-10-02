-- Prove2me | Theorems.Thm_Transcendence_exp_monomials_liouville_lower
-- name    : Transcendence.exp_monomials_liouville_lower
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:18:27.38417+00:00
-- url     : https://prove2.me/theorems/3e0a1030-aedc-4ace-a12b-8c4476667212
-- title:
--   Liouville's lower bound (4.14) for the non-zero derivatives of an integer combination of exponential monomials at lattice points
-- statement:
--   Let $\iota$ be a finite set, $k_0 \in \iota$ and $d_0 \le 1$, and let $x_1, \dots, x_{d_1}$ and $y_j$ ($j \in \iota$) be vectors in $\mathbb{C}^\iota$ such that every coordinate $x_{i\nu}$ and every $e^{\langle x_i, y_j\rangle}$ is algebraic and, if $d_0 = 1$, every $y_{jk_0}$ is algebraic; here $\langle w, z\rangle = \sum_\nu w_\nu z_\nu$. There is a constant $C \ge 1$ with the following property. Let $T \ge 1$ and $S_1$ be integers, $N \ge 0$, and
--
--   $$F(z) = \sum_{\tau, t} p_{\tau,t}\, z_{k_0}^{\tau}\, e^{\langle t_1x_1 + \dots + t_{d_1}x_{d_1},\, z\rangle} \qquad (0 \le \tau \le d_0T,\ t \in \{0, \dots, T\}^{d_1})$$
--
--   with integers $|p_{\tau,t}| \le e^{N}$. If the derivative $D$ of $F$ along a list of $k$ coordinate directions, at a point $\sum_j s_jy_j$ with $0 \le s_j < S_1$, is not zero, then
--
--   $$\log|D| \ge -C\bigl(N + k(1 + \log T) + T(S_1 + \log(1 + k))\bigr).$$
--
--   The proof of `Transcendence.schneider_lang_cartesian` sets it against two upper bounds: (4.16) for the derivatives of order less than $nET$, and the Schwarz step for the first non-vanishing one.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None: this is (4.14) of Waldschmidt's book (§4.6, step 2, p. 137) with $T_0 = d_0T$, $T_1 = T$, and a bracket of a slightly different shape from the book's $N + \|\sigma\|\log T_1 + T_0\log(S_1 + \|\sigma\|) + T_1S_1$. The number field $K$, a common denominator $\delta$ and a bound $H$ for the houses are built inside, and Liouville's inequality is `Transcendence.liouville_house`. The book states that $c_1$ can be computed explicitly; here $C = D\bigl(2 + 2(1 + d_1n)(\log\delta + \log H) + \log(d_1 + 1) + d_0 + d_1 + \log n\bigr)$, with $D = [K : \mathbb{Q}]$ and $n = |\iota|$. The field contains the coordinates of the $x_i$, which step 1 of the book leaves out of it. The contribution of this node is the formal proof.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, §4.6, step 2: (4.14) (p. 137). Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- **Liouville's lower bound (4.14) for exponential monomials at lattice points** (Waldschmidt, *Diophantine
Approximation on Linear Algebraic Groups*, §4.6). Let the coordinates of `x₁, …, x_{d₁} ∈ ℂ^ι` and the numbers
`exp ⟨xᵢ, y_j⟩` be algebraic, let `d₀ ≤ 1`, and if `d₀ = 1` let every `y_{j k₀}` be algebraic. There is a constant
`C ≥ 1` such that for all `T ≥ 1`, `S₁`, `N ≥ 0` and integers `p_{τ,t}` with `|p_{τ,t}| ≤ e^N` (`0 ≤ τ ≤ d₀T`,
`t ∈ {0, …, T}^{d₁}`), every non-zero mixed partial derivative `D` of order `k`, along the coordinate directions
`L 0, …, L (k-1)`, of `F(z) = Σ p_{τ,t} · z_{k₀}^τ · exp ⟨t₁x₁ + ⋯ + t_{d₁}x_{d₁}, z⟩` at a lattice point
`Σ_j s_j y_j` (`0 ≤ s_j < S₁`) satisfies `log |D| ≥ -C (N + k (1 + log T) + T (S₁ + log (1 + k)))`. -/
theorem exp_monomials_liouville_lower {ι : Type*} [Fintype ι] [DecidableEq ι] {d₁ : ℕ}
    (x : Fin d₁ → ι → ℂ) (hxalg : ∀ i ν, IsAlgebraic ℚ (x i ν)) (y : ι → ι → ℂ)
    (hexp : ∀ i j, IsAlgebraic ℚ (Complex.exp (∑ ν, x i ν * y j ν))) (k₀ : ι) {d₀ : ℕ}
    (hd₀ : d₀ ≤ 1) (hy₀ : d₀ = 1 → ∀ j, IsAlgebraic ℚ (y j k₀)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (T S₁ : ℕ) (p : Fin (d₀ * T + 1) × (Fin d₁ → Fin (T + 1)) → ℤ) (N : ℝ)
      (s : ι → Fin S₁) (k : ℕ) (L : Fin k → ι),
      1 ≤ T → 0 ≤ N → (∀ l, |(p l : ℝ)| ≤ Real.exp N) →
      iteratedFDeriv ℂ k (fun z : ι → ℂ => ∑ l, (p l : ℂ) * (z k₀ ^ (l.1 : ℕ) *
        Complex.exp (∑ ν, (∑ i, ((l.2 i : ℕ) : ℂ) * x i ν) * z ν))) (∑ j, ((s j : ℕ) : ℂ) • y j)
        (fun l => Pi.single (L l) 1) ≠ 0 →
      -(C * (N + k * (1 + Real.log T) + T * (S₁ + Real.log (1 + k)))) ≤
        Real.log ‖iteratedFDeriv ℂ k (fun z : ι → ℂ => ∑ l, (p l : ℂ) * (z k₀ ^ (l.1 : ℕ) *
          Complex.exp (∑ ν, (∑ i, ((l.2 i : ℕ) : ℂ) * x i ν) * z ν))) (∑ j, ((s j : ℕ) : ℂ) • y j)
          (fun l => Pi.single (L l) 1)‖ := by
  sorry

end Transcendence
