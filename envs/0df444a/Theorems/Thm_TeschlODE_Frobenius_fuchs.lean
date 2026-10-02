-- Prove2me | Theorems.Thm_TeschlODE_Frobenius_fuchs
-- name    : TeschlODE.Frobenius.fuchs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T11:19:26.688479+00:00
-- url     : https://prove2.me/theorems/ee2718cf-b9e8-4898-9298-2dca16d101e4
-- title:
--   Theorem 4.5 (Fuchs) — Frobenius fundamental system at a regular singular point
-- statement:
--   Consider the second-order linear equation
--   $$u''(z) + p(z)\,u'(z) + q(z)\,u(z) = 0 \qquad (4.20)$$
--   whose coefficients have poles of order at most one and two at $z = 0$:
--   $$p(z) = \frac1z \sum_{j \ge 0} p_j z^j, \qquad q(z) = \frac{1}{z^2} \sum_{j \ge 0} q_j z^j, \qquad (4.30)$$
--   with both series convergent for $|z| < R$. Let $\alpha_1, \alpha_2$ be the characteristic exponents (4.37) of $p_0, q_0$, ordered by $\operatorname{Re}\alpha_1 \ge \operatorname{Re}\alpha_2$. Then two cases can occur.
--
--   **Case 1.** If $\alpha_1 - \alpha_2 \notin \mathbb{N}_0$, a fundamental system of solutions is
--   $$u_j(z) = z^{\alpha_j} h_j(z), \qquad j = 1, 2. \qquad (4.48)$$
--
--   **Case 2.** If $\alpha_1 - \alpha_2 = m \in \mathbb{N}_0$, a fundamental system of solutions is
--   $$u_1(z) = z^{\alpha_1} h_1(z), \qquad u_2(z) = z^{\alpha_2} h_2(z) + c\,\log(z)\,u_1(z), \qquad (4.49)$$
--   with a constant $c \in \mathbb{C}$ that may be zero unless $m = 0$.
--
--   In both cases $h_1, h_2$ are analytic near $0$ with $h_j(0) = 1$, and the radius of convergence of their power series is at least the smaller of the radii of convergence for $p$ and $q$.
--
--   This is the central result of the Frobenius method: at a regular singular point the solutions are, up to a power $z^\alpha$ and possibly one logarithm, as regular as the coefficients. It covers the Bessel, Legendre and hypergeometric equations.
--
--   **Formalization Note.** The hypotheses are given by functions $P, Q$ holomorphic on the disc $|z| < R$ (`Metric.eball 0 R`, $R \in (0,\infty]$) with $z p(z) = P(z)$ and $z^2 q(z) = Q(z)$ for $0 < |z| < R$; then $p_0 = P(0)$, $q_0 = Q(0)$ and $(\alpha_1, \alpha_2)$ = `charExponents (P 0) (Q 0)`. Taking $R$ to be the smaller of the two radii of convergence gives the book's radius claim, which is expressed as: $h_1, h_2$ are holomorphic on the whole disc $|z| < R$ (equivalently, their power series at $0$ converge there). Solutions are required on the slit punctured disc $\{0 < |z| < R\} \setminus (-\infty, 0]$ (`slitDisc R`), where $z^\alpha$ and $\log z$ are the principal branches; they are not solutions on the full punctured disc. "Fundamental system" means two solutions (`IsSolution`) that are linearly independent over $\mathbb{C}$ on that domain. "$\alpha_1 - \alpha_2 \in \mathbb{N}_0$" is `∃ m : ℕ, α₁ - α₂ = m`; Case 2 is stated for every such $m$, with the extra clause $m = 0 \Rightarrow c \neq 0$ (the book's "$c$ might be zero unless $m = 0$").
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 119, Theorem 4.5

import Mathlib
import Definitions.Def_TeschlODE_Frobenius_slitDisc
import Definitions.Def_TeschlODE_Frobenius_IsSolution
import Definitions.Def_TeschlODE_Frobenius_charExponents

namespace TeschlODE.Frobenius

/-- Teschl, Theorem 4.5 (Fuchs), pp. 119–120. The coefficients of `u'' + p(z) u' + q(z) u = 0`
(4.20) have poles of order at most one and two at `0`: `z p(z) = P(z)`, `z² q(z) = Q(z)` on
`0 < |z| < R` with `P`, `Q` holomorphic on `|z| < R` (4.30) (`R` = any radius up to the smaller
radius of convergence of the two series; `R = ⊤` allowed). `(α₁, α₂)` are the characteristic
exponents (4.37) of `p₀ = P(0)`, `q₀ = Q(0)`.
Case 1, `α₁ − α₂ ∉ ℕ₀`: `u_j = z^{α_j} h_j(z)` (4.48) is a fundamental system.
Case 2, `α₁ − α₂ = m ∈ ℕ₀`: `u₁ = z^{α₁} h₁`, `u₂ = z^{α₂} h₂ + c log(z) u₁` (4.49) is a fundamental
system, with `c ≠ 0` if `m = 0`.
In both cases `h_j(0) = 1` and `h_j` is holomorphic on the whole disc `|z| < R` (radius of
convergence at least `R`). Solutions live on the slit punctured disc `slitDisc R` with the
principal branches of `z^α` and `log z`; "fundamental system" = two solutions linearly independent
over `ℂ` on that domain. -/
theorem fuchs (p q P Q : ℂ → ℂ) (R : ENNReal) (hR : 0 < R)
    (hP : DifferentiableOn ℂ P (Metric.eball (0 : ℂ) R))
    (hQ : DifferentiableOn ℂ Q (Metric.eball (0 : ℂ) R))
    (hpP : ∀ z ∈ Metric.eball (0 : ℂ) R, z ≠ 0 → z * p z = P z)
    (hqQ : ∀ z ∈ Metric.eball (0 : ℂ) R, z ≠ 0 → z ^ 2 * q z = Q z) :
    ((∀ m : ℕ, (charExponents (P 0) (Q 0)).1 - (charExponents (P 0) (Q 0)).2 ≠ m) →
      ∃ h₁ h₂ : ℂ → ℂ,
        DifferentiableOn ℂ h₁ (Metric.eball (0 : ℂ) R) ∧
        DifferentiableOn ℂ h₂ (Metric.eball (0 : ℂ) R) ∧ h₁ 0 = 1 ∧ h₂ 0 = 1 ∧
        IsSolution p q (slitDisc R) (fun z => z ^ (charExponents (P 0) (Q 0)).1 * h₁ z) ∧
        IsSolution p q (slitDisc R) (fun z => z ^ (charExponents (P 0) (Q 0)).2 * h₂ z) ∧
        ∀ a b : ℂ, (∀ z ∈ slitDisc R,
            a * (z ^ (charExponents (P 0) (Q 0)).1 * h₁ z) +
              b * (z ^ (charExponents (P 0) (Q 0)).2 * h₂ z) = 0) → a = 0 ∧ b = 0) ∧
    (∀ m : ℕ, (charExponents (P 0) (Q 0)).1 - (charExponents (P 0) (Q 0)).2 = m →
      ∃ (h₁ h₂ : ℂ → ℂ) (c : ℂ), (m = 0 → c ≠ 0) ∧
        DifferentiableOn ℂ h₁ (Metric.eball (0 : ℂ) R) ∧
        DifferentiableOn ℂ h₂ (Metric.eball (0 : ℂ) R) ∧ h₁ 0 = 1 ∧ h₂ 0 = 1 ∧
        IsSolution p q (slitDisc R) (fun z => z ^ (charExponents (P 0) (Q 0)).1 * h₁ z) ∧
        IsSolution p q (slitDisc R) (fun z => z ^ (charExponents (P 0) (Q 0)).2 * h₂ z +
          c * Complex.log z * (z ^ (charExponents (P 0) (Q 0)).1 * h₁ z)) ∧
        ∀ a b : ℂ, (∀ z ∈ slitDisc R,
            a * (z ^ (charExponents (P 0) (Q 0)).1 * h₁ z) +
              b * (z ^ (charExponents (P 0) (Q 0)).2 * h₂ z +
                c * Complex.log z * (z ^ (charExponents (P 0) (Q 0)).1 * h₁ z)) = 0) →
            a = 0 ∧ b = 0) := by sorry

end TeschlODE.Frobenius
