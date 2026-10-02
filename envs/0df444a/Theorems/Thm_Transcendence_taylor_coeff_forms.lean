-- Prove2me | Theorems.Thm_Transcendence_taylor_coeff_forms
-- name    : Transcendence.taylor_coeff_forms
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:19:11.270067+00:00
-- url     : https://prove2.me/theorems/545622c4-c143-48c2-a85d-280d5d1be38f
-- title:
--   The Taylor polynomial of Σ c_λ φ_λ at 0 as linear forms in the c_λ, with coefficients bounded by Cauchy's inequalities
-- statement:
--   Let $\iota$ and $\Lambda$ be finite sets, let $\varphi_\lambda$ ($\lambda \in \Lambda$) be entire functions on $\mathbb{C}^\iota$ with $|\varphi_\lambda| \le B_\lambda$ on the closed polydisc of radius $r > 0$ about $0$, and let $T \in \mathbb{N}$. There are complex numbers $u_{\tau\lambda}$, for $\lambda \in \Lambda$ and multi-indices $\tau$ in the box $\{0, \dots, T-1\}^\iota$, with $|u_{\tau\lambda}| \le B_\lambda$, such that for all $c \in \mathbb{C}^\Lambda$ and $z \in \mathbb{C}^\iota$ the function $F = \sum_\lambda c_\lambda\varphi_\lambda$ satisfies
--
--   $$\sum_{k < T}\frac{1}{k!}\,D^kF(0)(z, \dots, z) = \sum_{\tau}\Bigl(\sum_{\lambda} u_{\tau\lambda}\,c_\lambda\Bigr)\prod_{\nu \in \iota}\Bigl(\frac{z_\nu}{r}\Bigr)^{\tau_\nu},$$
--
--   where $D^kF$ is the $k$-th Fréchet derivative.
--
--   The $T^n$ linear forms $c \mapsto \sum_\lambda u_{\tau\lambda}c_\lambda$ ($n = |\iota|$) are those to which Thue–Siegel's lemma is applied in the proof of Proposition 4.10 (`Transcendence.siegel_small_values_of_count`); when they are small, so is the Taylor polynomial of $F$ on the polydisc of radius $r$.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None: a step of the proof of Proposition 4.10 of Waldschmidt's book (p. 135), where $u_{\tau\lambda}$ is $D^\tau\varphi_\lambda(0)\,r^{\|\tau\|}/\tau!$ times $2T^n$, bounded by Cauchy's inequalities (p. XVII), here `Transcendence.polydisc_cauchy`. The forms are indexed by the box $\{0, \dots, T-1\}^\iota$, with $T^n$ elements, the number that the book uses as a bound for the number of $\tau$ with $\|\tau\| < T$. The contribution of this node is the formal proof.
-- source:
--   A step of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Proposition 4.10 (p. 135), with Cauchy's inequalities (p. XVII). Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- **Cauchy-bounded Taylor coefficients as linear forms** (Waldschmidt, *Diophantine Approximation on
Linear Algebraic Groups*, proof of Prop. 4.10 and Lemma 4.13; Cauchy's inequalities, p. XVII). Let `φ_λ`
(`λ ∈ Λ`) be entire functions on `ℂ^ι` with `|φ_λ| ≤ B_λ` on the closed polydisc of radius `r > 0` (the
sup-norm ball). There are complex numbers `u_{τλ}`, indexed by the multi-indices `τ` in the box
`{0, …, T-1}^ι`, with `|u_{τλ}| ≤ B_λ`, such that for every combination `Σ_λ c_λ φ_λ` the Taylor polynomial
of order `< T` at `0`, whose `k`-th term is `D^k F(0)(z, …, z) / k!`, equals
`Σ_τ (Σ_λ u_{τλ} c_λ) ∏_ν (z_ν / r)^{τ_ν}`. -/
theorem taylor_coeff_forms {ι Λ : Type*} [Fintype ι] [DecidableEq ι] [Fintype Λ]
    (φ : Λ → (ι → ℂ) → ℂ) (hφ : ∀ l, AnalyticOnNhd ℂ (φ l) Set.univ) {r : ℝ} (hr : 0 < r)
    (B : Λ → ℝ) (hB : ∀ l, ∀ z ∈ Metric.closedBall (0 : ι → ℂ) r, ‖φ l z‖ ≤ B l) (T : ℕ) :
    ∃ u : (ι → Fin T) → Λ → ℂ, (∀ τ l, ‖u τ l‖ ≤ B l) ∧
      ∀ (c : Λ → ℂ) (z : ι → ℂ),
        ∑ k ∈ Finset.range T, (k.factorial : ℂ)⁻¹ *
            iteratedFDeriv ℂ k (fun x => ∑ l, c l * φ l x) 0 (fun _ => z) =
          ∑ τ, (∏ ν, (z ν / r) ^ (τ ν : ℕ)) * ∑ l, u τ l * c l := by
  sorry

end Transcendence
