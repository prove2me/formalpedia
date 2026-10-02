-- Prove2me | Theorems.Thm_TeschlODE_Frobenius_fuchs_characterization
-- name    : TeschlODE.Frobenius.fuchs_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T11:18:43.860421+00:00
-- url     : https://prove2.me/theorems/13fac949-9598-498d-96b7-e19df18269fd
-- title:
--   Theorem 4.6 (Fuchs) — Frobenius-type fundamental systems exist iff p and zq have at most simple poles
-- statement:
--   Let $R \in (0, \infty]$ and let $p, q$ be holomorphic in the punctured disc $0 < |z| < R$. Then the equation
--   $$u'' + p(z)\,u' + q(z)\,u = 0 \qquad (4.20)$$
--   has two solutions $u_1, u_2$ as in Theorem 4.5, namely a fundamental system of the form
--   $$u_1(z) = z^{\alpha_1} h_1(z), \qquad u_2(z) = z^{\alpha_2} h_2(z) + c\,\log(z)\,u_1(z),$$
--   with $\alpha_1, \alpha_2, c \in \mathbb{C}$ and $h_1, h_2$ analytic near $0$ with $h_j(0) = 1$, if and only if $p(z)$ and $z\,q(z)$ have at most first-order poles at $0$.
--
--   So the hypothesis of Fuchs's theorem is not only sufficient but also necessary: a singular point admits a fundamental system of Frobenius type exactly when it is a regular singular point.
--
--   **Formalization Note.** The solutions are required on some slit punctured disc $\{0 < |z| < \rho\} \setminus (-\infty, 0]$ with $0 < \rho \le R$ (`slitDisc ρ`), with the principal branches of $z^\alpha$ and $\log z$, and to be linearly independent over $\mathbb{C}$ there. Case 1 of Theorem 4.5 is the form with $c = 0$, so "as in the previous theorem" is read as "of the form (4.49) for some $\alpha_1, \alpha_2, c$"; the exponents are not required to be the characteristic exponents (they are forced to be). Poles are `HasPoleOfOrderAtMost p 1` and `HasPoleOfOrderAtMost (fun z => z * q z) 1`.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 121, Theorem 4.6

import Mathlib
import Definitions.Def_TeschlODE_Frobenius_slitDisc
import Definitions.Def_TeschlODE_Frobenius_IsSolution
import Definitions.Def_TeschlODE_Frobenius_HasPoleOfOrderAtMost

namespace TeschlODE.Frobenius

/-- Teschl, Theorem 4.6 (Fuchs), p. 121: for `p`, `q` holomorphic in a punctured disc
`0 < |z| < R`, the equation (4.20) has two solutions of the form of Theorem 4.5,
`u₁ = z^{α₁} h₁(z)`, `u₂ = z^{α₂} h₂(z) + c log(z) u₁(z)` with `h_j` analytic at `0`, `h_j(0) = 1`,
forming a fundamental system on some slit punctured disc `slitDisc ρ`, `0 < ρ ≤ R` (principal
branches), if and only if `p(z)` and `z q(z)` have at most first-order poles at `0`. Case 1 of
Theorem 4.5 is the form with `c = 0`. -/
theorem fuchs_characterization (p q : ℂ → ℂ) (R : ENNReal) (hR : 0 < R)
    (hp : DifferentiableOn ℂ p (Metric.eball (0 : ℂ) R \ {0}))
    (hq : DifferentiableOn ℂ q (Metric.eball (0 : ℂ) R \ {0})) :
    (∃ ρ : ENNReal, 0 < ρ ∧ ρ ≤ R ∧ ∃ (α₁ α₂ c : ℂ) (h₁ h₂ : ℂ → ℂ),
        AnalyticAt ℂ h₁ 0 ∧ AnalyticAt ℂ h₂ 0 ∧ h₁ 0 = 1 ∧ h₂ 0 = 1 ∧
        IsSolution p q (slitDisc ρ) (fun z => z ^ α₁ * h₁ z) ∧
        IsSolution p q (slitDisc ρ) (fun z => z ^ α₂ * h₂ z + c * Complex.log z * (z ^ α₁ * h₁ z)) ∧
        ∀ a b : ℂ, (∀ z ∈ slitDisc ρ,
            a * (z ^ α₁ * h₁ z) + b * (z ^ α₂ * h₂ z + c * Complex.log z * (z ^ α₁ * h₁ z)) = 0) →
          a = 0 ∧ b = 0) ↔
    HasPoleOfOrderAtMost p 1 ∧ HasPoleOfOrderAtMost (fun z => z * q z) 1 := by sorry

end TeschlODE.Frobenius
