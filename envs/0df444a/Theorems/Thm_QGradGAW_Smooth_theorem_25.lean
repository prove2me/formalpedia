-- Prove2me | Theorems.Thm_QGradGAW_Smooth_theorem_25
-- name    : QGradGAW.Smooth.theorem_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:00.075193+00:00
-- url     : https://prove2.me/theorems/68a58e34-1746-427b-a5f0-88c6fa60d794
-- title:
--   Theorem 25, p. 29 — an ε-approximate gradient of an analytic f with |∂_α f(x)| ≤ cᵏk^{k/2}, with probability ≥ 1 − δ, from Õ((c√d/ε) log(d/δ)) phase queries
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $d\ge1$, $0<\varepsilon\le c$ and $\delta>0$. Then there are parameters $m,n_\varepsilon,n_M,T\in\mathbb N$ and $r>0$ of the central-difference version of Jordan's algorithm, depending only on $d,c,\varepsilon,\delta$, such that
--
--   1. the algorithm makes at most
--   $$C\,\frac{c\sqrt d}{\varepsilon}\,\log\Big(2+\frac{c\sqrt d}{\varepsilon}\Big)\,\log\Big(2+\log\Big(2+\frac{c\sqrt d}{\varepsilon}\Big)\Big)\,\log\Big(2+\frac d\delta\Big)$$
--   fractional queries to the phase oracle $O_f$, that is $\widetilde O\big(\frac{c\sqrt d}{\varepsilon}\log\frac d\delta\big)$; and
--   2. for every point $x\in\mathbb R^d$ and every smooth $f:\mathbb R^d\to\mathbb R$ that is analytic around $x$ and satisfies
--   $$|\partial_\alpha f(x)|\le c^k\,k^{k/2}\qquad\text{for all }k\ge1,\ \alpha\in[d]^k,$$
--   the algorithm outputs $\tilde\nabla f(x)\in\mathbb R^d$ with
--   $$\big\|\nabla f(x)-\tilde\nabla f(x)\big\|_\infty\le\varepsilon$$
--   with probability at least $1-\delta$.
--
--   The algorithm runs Jordan's algorithm on the degree-$2m$ central difference of $g(y)=f(x+y)$ on a grid of edge length $r$, repeats it $T$ times and takes the coordinate-wise median. This is the paper's main upper bound: a quadratic improvement in $d$ over classical finite differences for this function class, and nearly linear dependence on $1/\varepsilon$.
--
--   **Formalization Note** The constant $C$ comes first and the parameters are chosen before $x$ and $f$ ("a quantum algorithm that works for all such functions"). The $\widetilde O$ is made explicit as the bound of display (26), $\frac{c\sqrt d}{\varepsilon}\,m\log m$ with $m\approx\log\frac{c\sqrt d}{\varepsilon}$, times the $O(\log(d/\delta))$ repetitions of Theorem 21; the "$2+$" inside each logarithm keeps it at least $\log 2$, which changes only the constant since $c\sqrt d/\varepsilon\ge1$. **Queries** are counted as $T\sum_{\ell=-m}^m\lceil 2\pi 2^{n_\varepsilon}|a^{(2m)}_\ell|\rceil$: each run applies the oracle $e^{2\pi i 2^{n_\varepsilon}\sum_\ell a_\ell^{(2m)} f(x+\ell rz)}$, and its factor for $\ell$ costs $\lceil 2\pi 2^{n_\varepsilon}|a_\ell^{(2m)}|\rceil$ fractional queries $O_f^s$, $|s|\le1$ (Definition 11 and display (25)). "Analytic" (footnote 19: $f$ defined on all of $\mathbb R^d$) is the Taylor representation (5) around $x$ together with $C^\infty$ smoothness. The derivative bound is for $k\ge1$ because the paper's $\mathbb N$ starts at $1$. Gate complexity is not formalized.
-- source:
--   Gilyén, Arunachalam, Wiebe, Optimizing quantum optimization algorithms via faster quantum gradient computation, arXiv:1711.00465v3, p. 29, Theorem 25; proof pp. 29–30, displays (25)–(26)

import Mathlib
import Definitions.Def_QGradGAW_Smooth_Setting

namespace QGradGAW.Smooth

/-- arXiv:1711.00465v3, p. 29, Theorem 25: there is an absolute constant `C` such that for every
`d ∈ ℕ₊`, `0 < ε ≤ c` and `δ > 0` there are parameters `(m, n_ε, n_M, T, r)` of the
central-difference Jordan algorithm `gradAlgFailProb`, chosen before the function, whose
number of fractional phase queries to `O_f` (`queryCount`) is
`O((c√d/ε) log(c√d/ε) log log(c√d/ε) · log(d/δ))` and which, for every `x ∈ ℝ^d` and every
`f : ℝ^d → ℝ` that is analytic around `x` with `|∂_α f(x)| ≤ c^k k^{k/2}` for all
`k ∈ ℕ₊`, `α ∈ [d]^k`, outputs `∇̃f(x)` with `‖∇f(x) − ∇̃f(x)‖∞ ≤ ε` with probability at
least `1 − δ`. -/
theorem theorem_25 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 1 ≤ d → ∀ c ε δ : ℝ, 0 < ε → ε ≤ c → 0 < δ →
      ∃ (m nε nM T : ℕ) (r : ℝ), 0 < r ∧
        (queryCount m nε T : ℝ) ≤ C * (c * Real.sqrt d / ε) * Real.log (2 + c * Real.sqrt d / ε) *
          Real.log (2 + Real.log (2 + c * Real.sqrt d / ε)) * Real.log (2 + d / δ) ∧
        ∀ (x : Fin d → ℝ) (f : (Fin d → ℝ) → ℝ),
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → IsTaylorRep f x →
          (∀ k : ℕ, 1 ≤ k → ∀ α : Fin k → Fin d,
            |partialAlpha f k α x| ≤ c ^ k * Real.sqrt k ^ k) →
          gradAlgFailProb d m nε nM T r f x ε ≤ δ := by sorry

end QGradGAW.Smooth
