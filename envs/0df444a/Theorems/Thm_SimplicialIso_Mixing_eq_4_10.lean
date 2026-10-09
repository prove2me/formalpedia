-- Prove2me | Theorems.Thm_SimplicialIso_Mixing_eq_4_10
-- name    : SimplicialIso.Mixing.eq_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:39.015455+00:00
-- url     : https://prove2.me/theorems/b98e47f3-73e7-4aa2-a583-0f000ebf8d74
-- title:
--   (4.10), p. 18 — the largest |μ| over Spec((αI − Δ⁺)|_{Z_{d−1}}) equals ‖(αI − Δ⁺)|_{Z_{d−1}}‖
-- statement:
--   Let $X$ be a $d$-dimensional complex with a complete skeleton on $n$ vertices, $d\ge1$, and $\alpha\in\mathbb R$. The operator $\alpha I-\Delta^+$ maps $Z_{d-1}$ to itself, and
--   $$\max\bigl\{|\mu|\;\big|\;\mu\in\operatorname{Spec}(\alpha I-\Delta^+)\big|_{Z_{d-1}}\bigr\}=\bigl\|(\alpha I-\Delta^+)\big|_{Z_{d-1}}\bigr\|.\qquad(4.10)$$
--   Equivalently: for every real $\rho$, every eigenvalue $\mu$ of $\alpha I-\Delta^+$ on $Z_{d-1}$ satisfies $|\mu|\le\rho$ if and only if $\|(\alpha I-\Delta^+)g\|\le\rho\|g\|$ for every $g\in Z_{d-1}$.
--
--   This lets the spectral quantity $\rho_\alpha$ of the Mixing Lemma bound the error term of (4.8).
--
--   **Formalization Note.** Lean states the equivalent "same upper bounds" form, which avoids a maximum or supremum that would default to $0$ on an empty set (if $Z_{d-1}=0$, both sides hold for every $\rho$). The first expression for $\rho_\alpha$ in (4.10), $\max\{|\mu_{\binom{n-1}{d-1}}|,|\mu_m|\}$, rests on Proposition 3.3 ($\dim B^{d-1}=\binom{n-1}{d-1}$) and is not formalized.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, §4.3, p. 18, equation (4.10), second equality

import Mathlib
import Definitions.Def_SimplicialIso_Mixing_Setting

namespace SimplicialIso.Mixing

open Finset
open scoped InnerProductSpace

/-- (4.10), p. 18, second equality: `max {|μ| : μ ∈ Spec((αI − Δ⁺)|_{Z_{d-1}})}` equals the
operator norm `‖(αI − Δ⁺)|_{Z_{d-1}}‖`, stated as: a real `ρ` bounds every eigenvalue of
`αI − Δ⁺` on `Z_{d-1}` in absolute value if and only if `‖(αI − Δ⁺) g‖ ≤ ρ ‖g‖` for every
`g ∈ Z_{d-1}`. -/
theorem eq_4_10 (n d : ℕ) (hd : 1 ≤ d) (X : Complex n d) (α ρ : ℝ) :
    (∀ μ, IsCycleEigenvalue (α • LinearMap.id - upLap X) μ → |μ| ≤ ρ) ↔
      ∀ g ∈ cycles n d, ‖(α • LinearMap.id - upLap X : Form n d →ₗ[ℝ] Form n d) g‖ ≤ ρ * ‖g‖ := by sorry

end SimplicialIso.Mixing
