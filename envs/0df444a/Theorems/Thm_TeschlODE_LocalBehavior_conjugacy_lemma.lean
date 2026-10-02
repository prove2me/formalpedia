-- Prove2me | Theorems.Thm_TeschlODE_LocalBehavior_conjugacy_lemma
-- name    : TeschlODE.LocalBehavior.conjugacy_lemma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T17:33:15.993515+00:00
-- url     : https://prove2.me/theorems/ccdc2849-0803-416f-a58b-94da9f881ec4
-- title:
--   Lemma 9.7 — global conjugacy ϕ ∘ A = (A + g) ∘ ϕ for bounded, ε-Lipschitz g
-- statement:
--   Let $A$ be an invertible real $n \times n$ matrix with no eigenvalue on the unit circle. Let $E^+ = E^+(A)$ (eigenvalues inside the unit circle) and $E^- = E^-(A)$ (outside), $A_\pm = A|_{E^\pm}$, so $\mathbb{R}^n = E^+ \oplus E^-$. Let $N$ be a norm on $\mathbb{R}^n$ and $\alpha < 1$ with
--   $$N(A x) \le \alpha N(x) \ (x \in E^+), \qquad N(A^{-1} x) \le \alpha N(x) \ (x \in E^-),$$
--   i.e. $\max(\|A_-^{-1}\|, \|A_+\|) \le \alpha$ in the operator norms of $N$, and such that $N(x^\pm) \le N(x^+ + x^-)$ for $x^\pm \in E^\pm$. Let $g : \mathbb{R}^n \to \mathbb{R}^n$ be bounded with
--   $$N(g(x) - g(y)) \le \varepsilon N(x - y), \qquad \varepsilon < \frac{1 - \alpha}{2}. \qquad (9.30)$$
--   Then there is a unique continuous bounded $h$ such that $\phi = \mathrm{id} + h$ satisfies
--   $$\phi \circ A = f \circ \phi, \qquad f = A + g. \qquad (9.31)$$
--   If $f$ is invertible, then $\phi$ is a homeomorphism, and if in addition $g(0) = 0$ then $\phi(0) = 0$. Moreover $f$ is invertible whenever $\varepsilon \|A^{-1}\| < 1$.
--
--   This is the analytic core of the Hartman–Grobman theorem: both the version for maps (Theorem 10.4) and for flows (Theorem 9.9) reduce to it after cutting off the nonlinearity.
--
--   **Formalization Note.** The book's $\alpha = \max(\|A_-^{-1}\|, \|A_+\|)$ (with $\|A_-^{-1}\| = 0$ when $E^- = 0$) is the least number satisfying the two displayed bounds, so quantifying over every $\alpha < 1$ satisfying them is equivalent (the constraint $\varepsilon < (1-\alpha)/2$ is weakest at the least $\alpha$). Likewise "$\varepsilon\|A^{-1}\| < 1$" is read as: for every $\beta$ with $N(A^{-1}x) \le \beta N(x)$ for all $x$, $\varepsilon\beta < 1$ implies $f$ bijective. The equation (9.31) is written pointwise, $Ax + h(Ax) = A(x + h(x)) + g(x + h(x))$. "Bounded" is measured in $N$ (all norms on $\mathbb{R}^n$ are equivalent). **Added hypothesis:** $N(x^\pm) \le N(x^+ + x^-)$, i.e. the projections onto $E^\pm$ along $E^\mp$ have $N$-norm at most $1$. The book's proof uses it when it bounds $\|L^{-1}\| \le \frac{2}{1-\alpha}$ from $\|L_\pm^{-1}\| \le \frac{1}{1-\alpha}$ via the splitting $C(\mathbb{R}^n, \mathbb{R}^n) = C(\mathbb{R}^n, E^-) \oplus C(\mathbb{R}^n, E^+)$; it holds for the norms the book's construction produces (e.g. $\max(N_+(x^+), N_-(x^-))$ of norms on the two summands, as in Problem 3.48). Without it the printed lemma is false: for $A = \mathrm{diag}(1/2, 2)$ on $\mathbb{R}^2$ and $N(x) = |Tx|_2$ with $T = \begin{pmatrix}1&1\\0&1/4\end{pmatrix}$ one has $\alpha = 1/2$, yet the linear map $G = T^{-1}\begin{pmatrix}0&0\\-1/12&0\end{pmatrix}T$ has $N$-norm $1/12$ and $A + G$ has eigenvalue $1$; for $g = G \circ r$ ($r$ the radial retraction onto the $N$-unit ball; $g$ bounded, $\varepsilon = 1/6 < 1/4$), $f$ fixes a segment of points $p$, and a continuous $\phi = \mathrm{id} + h$ with $h$ bounded would be onto, with each compact $\phi^{-1}(p)$ invariant under $A$, hence inside $E^+$ and containing $0$, so $\phi(0) = p$ for every such $p$, which is impossible.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 262, Lemma 9.7

import Mathlib
import Definitions.Def_TeschlODE_LocalBehavior_eigenvalues
import Definitions.Def_TeschlODE_LocalBehavior_spectralSubspace
import Definitions.Def_TeschlODE_LocalBehavior_IsNorm

namespace TeschlODE.LocalBehavior

/-- Teschl, Lemma 9.7, pp. 262–263. `A` is an invertible real matrix with no eigenvalue on the
unit circle; `E₊ = E₊(A)` (eigenvalues inside the unit circle, `A₊ = A|E₊` contracting) and
`E₋ = E₋(A)` (outside, `A₋ = A|E₋` expanding). `N` is a norm on `ℝⁿ` in which
`‖A₊‖ ≤ α` and `‖A₋⁻¹‖ ≤ α` with `α < 1` (the book's `α = max(‖A₋⁻¹‖, ‖A₊‖)` is the least such
`α`), and in which the splitting `ℝⁿ = E₊ ⊕ E₋` does not increase norms (`N x₊ ≤ N (x₊ + x₋)`,
`N x₋ ≤ N (x₊ + x₋)`; the book's proof uses this for `‖L⁻¹‖ ≤ 2/(1-α)`). Then for every
bounded `g` with `N (g x - g y) ≤ ε N (x - y)`, `ε < (1-α)/2` (9.30), there is a unique
continuous bounded `h` with `ϕ ∘ A = f ∘ ϕ` for `ϕ = id + h`, `f = A + g` (9.31). If `f` is
invertible, `ϕ` is a homeomorphism, and if moreover `g 0 = 0` then `ϕ 0 = 0`. Finally
`ε ‖A⁻¹‖ < 1` makes `f` invertible. -/
theorem conjugacy_lemma {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hAinv : IsUnit A)
    (hA : ∀ z ∈ eigenvalues A, ‖z‖ ≠ 1)
    (N : (Fin n → ℝ) → ℝ) (hN : IsNorm N)
    (hsplit : ∀ x ∈ spectralSubspace A {z | ‖z‖ < 1}, ∀ y ∈ spectralSubspace A {z | 1 < ‖z‖},
      N x ≤ N (x + y) ∧ N y ≤ N (x + y))
    (α : ℝ) (hα : α < 1)
    (hAs : ∀ x ∈ spectralSubspace A {z | ‖z‖ < 1}, N (A.mulVec x) ≤ α * N x)
    (hAu : ∀ x ∈ spectralSubspace A {z | 1 < ‖z‖}, N (A⁻¹.mulVec x) ≤ α * N x)
    (g : (Fin n → ℝ) → (Fin n → ℝ)) (hgb : ∃ C : ℝ, ∀ x, N (g x) ≤ C)
    (ε : ℝ) (hε : ε < (1 - α) / 2) (hg : ∀ x y, N (g x - g y) ≤ ε * N (x - y)) :
    ∃ h : (Fin n → ℝ) → (Fin n → ℝ),
      (Continuous h ∧ (∃ C : ℝ, ∀ x, N (h x) ≤ C) ∧
        ∀ x, A.mulVec x + h (A.mulVec x) = A.mulVec (x + h x) + g (x + h x)) ∧
      (∀ h' : (Fin n → ℝ) → (Fin n → ℝ), Continuous h' → (∃ C : ℝ, ∀ x, N (h' x) ≤ C) →
        (∀ x, A.mulVec x + h' (A.mulVec x) = A.mulVec (x + h' x) + g (x + h' x)) → h' = h) ∧
      (Function.Bijective (fun x => A.mulVec x + g x) →
        (∃ ϕ : (Fin n → ℝ) ≃ₜ (Fin n → ℝ), ∀ x, ϕ x = x + h x) ∧ (g 0 = 0 → h 0 = 0)) ∧
      (∀ β : ℝ, (∀ x, N (A⁻¹.mulVec x) ≤ β * N x) → ε * β < 1 →
        Function.Bijective (fun x => A.mulVec x + g x)) := by sorry

end TeschlODE.LocalBehavior
