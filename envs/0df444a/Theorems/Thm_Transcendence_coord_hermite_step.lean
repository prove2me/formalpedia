-- Prove2me | Theorems.Thm_Transcendence_coord_hermite_step
-- name    : Transcendence.coord_hermite_step
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:17:57.262618+00:00
-- url     : https://prove2.me/theorems/88e63d37-3daa-47b5-a7c1-54ccbc4f22bc
-- title:
--   One step of Schwarz's lemma for Cartesian products: an entire function replaced by its Hermite interpolant in one variable, with bounds
-- statement:
--   Let $g$ be an entire function on $\mathbb{C}^\iota$ ($\iota$ finite) with $|g| \le K$ on the closed polydisc of radius $R$, let $i \in \iota$ and $S_0 \in \mathbb{N}$, and let $E$ be a finite set of complex numbers $\zeta$ with $|\zeta| \le r$, where $0 < r$ and $5r \le R$; put $p = |E|S_0$. There is an entire function $h$ on $\mathbb{C}^\iota$ such that:
--
--   - $|h| \le 3^{p}K$ on the closed polydisc of radius $R$;
--   - $|g - h| \le (2r)^{p}(3/R)^{p}K$ on the closed polydisc of radius $r$;
--   - for every point $\xi$ and all coordinate directions $v_0, \dots, v_{m-1}$ different from $i$: if, for every $\zeta \in E$ and every $k < S_0$, the derivative of $g$ of order $m + k$ along $e_{v_0}, \dots, e_{v_{m-1}}$ followed by $k$ times $e_i$ vanishes at $\xi[i := \zeta]$, then the derivative of $h$ of order $m$ along $e_{v_0}, \dots, e_{v_{m-1}}$ vanishes at $\xi$.
--
--   Here $\xi[i := \zeta]$ is $\xi$ with its coordinate $\xi_i$ replaced by $\zeta$, the polydiscs are centred at $0$, and the derivatives are values of `iteratedFDeriv` on the coordinate vectors $e_\nu$.
--
--   In the proof, $h$ is the Hermite interpolant of $g$ in the variable $z_i$ at the nodes of $E$, each with multiplicity $S_0$. Applied in each coordinate in turn, it proves `Transcendence.cartesian_schwarz`.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None: a step of the proof of Proposition 4.7 of Waldschmidt's book (pp. 122–130). It does the work of Lemma 4.8 in the book's case $m = n$, with the bounds of Step 2.4, one coordinate at a time. The book's route goes through the ideal of Lemma 4.8 in all the variables at once, and its Step 2.1 uses Osgood's lemma and asserts the continuity of $f/P(z_n)$ without proof; here only the remainder has to be entire in all the variables, and the quotient is only bounded, slice by slice, so only one-variable complex analysis is used. The contribution of this node is the formal proof.
-- source:
--   A step of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Proposition 4.7 (pp. 122–130): the case m = n of Lemma 4.8 (pp. 123–126) in one coordinate, with the bounds of Step 2.4. Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- **One step of Schwarz's lemma for Cartesian products** (Waldschmidt, *Diophantine Approximation on Linear
Algebraic Groups*, proof of Prop. 4.7: Lemma 4.8 in one variable, with explicit bounds). Let `g` be an entire
function of the variables `z_ν` (`ν ∈ ι`) with `|g| ≤ K` on the closed polydisc of radius `R`, let `i ∈ ι`, and
let `E` be a finite set of points in the closed disc of radius `r > 0`, where `R ≥ 5r`; put `p = |E|·S₀`. There
is an entire function `h` (the Hermite interpolant of `g` in the variable `z_i` at the nodes `E`, each of
multiplicity `S₀`) with `|h| ≤ 3^p·K` on the polydisc of radius `R` and `|g - h| ≤ (2r)^p·(3/R)^p·K` on the
polydisc of radius `r`, and through which derivatives in the other variables pass: the derivative of `h` at `ξ`
along the coordinate directions `v 0, …, v (m-1)`, all different from `i`, vanishes as soon as, for every
`ζ ∈ E` and `k < S₀`, the derivative of `g` along `v 0, …, v (m-1)` followed by `k` times `i` vanishes at the
point `ξ` with its coordinate `ξ_i` replaced by `ζ`. -/
theorem coord_hermite_step {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : (ι → ℂ) → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ) (i : ι) (E : Finset ℂ) (S₀ : ℕ)
    {r R K : ℝ} (hr : 0 < r) (hR : 5 * r ≤ R) (hE : ∀ ζ ∈ E, ‖ζ‖ ≤ r)
    (hK : ∀ y ∈ Metric.closedBall (0 : ι → ℂ) R, ‖g y‖ ≤ K) :
    ∃ h : (ι → ℂ) → ℂ, AnalyticOnNhd ℂ h Set.univ ∧
      (∀ z ∈ Metric.closedBall (0 : ι → ℂ) R, ‖h z‖ ≤ 3 ^ (E.card * S₀) * K) ∧
      (∀ z ∈ Metric.closedBall (0 : ι → ℂ) r,
        ‖g z - h z‖ ≤ (2 * r) ^ (E.card * S₀) * ((3 / R) ^ (E.card * S₀) * K)) ∧
      ∀ (m : ℕ) (v : Fin m → ι), (∀ t, v t ≠ i) → ∀ ξ : ι → ℂ,
        (∀ ζ ∈ E, ∀ k < S₀, iteratedFDeriv ℂ (m + k) g (Function.update ξ i ζ)
          (fun t => Pi.single (Fin.append v (fun _ : Fin k => i) t) 1) = 0) →
        iteratedFDeriv ℂ m h ξ (fun t => Pi.single (v t) 1) = 0 := by
  sorry

end Transcendence
