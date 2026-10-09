-- Prove2me | Theorems.Thm_SimplicialIso_Mixing_eq_4_11
-- name    : SimplicialIso.Mixing.eq_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:28.238158+00:00
-- url     : https://prove2.me/theorems/c485cf79-6b5a-479d-952a-b2e0e9726cd4
-- title:
--   (4.11), p. 18 — |⟨φ, (αI − Δ⁺)ℙ_{Z_{d−1}}ψ⟩| ≤ ρ_α√(|A_0||A_d|)|A_1|⋯|A_{d−1}|
-- statement:
--   Let $X$, $d\ge1$, the pairwise disjoint sets $A_0,\dots,A_d$ and $\varphi,\psi$ be as in (4.6), and $\alpha\in\mathbb R$. Let $\rho$ be a real number with $|\mu|\le\rho$ for every eigenvalue $\mu$ of $\alpha I-\Delta^+$ on $Z_{d-1}$; the least such $\rho$ is $\rho_\alpha$. Then
--   $$\bigl|\langle\varphi,(\alpha I-\Delta^+)\mathbb P_{Z_{d-1}}\psi\rangle\bigr|\le\rho\sqrt{|A_0|\,|A_d|}\;|A_1|\,|A_2|\cdots|A_{d-1}|.\qquad(4.11)$$
--
--   This bounds the error term of (4.8).
--
--   **Formalization Note.** $\rho_\alpha$ is not defined as a maximum; the statement holds for every upper bound $\rho$ of the absolute eigenvalues on $Z_{d-1}$, which is equivalent to stating it for $\rho_\alpha$. The product $|A_1|\cdots|A_{d-1}|$ runs over the indices other than $0$ and $d$, and is $1$ when $d=1$.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, §4.3, p. 18, equation (4.11)

import Mathlib
import Definitions.Def_SimplicialIso_Mixing_Setting
import Definitions.Def_SimplicialIso_Mixing_DeltaForms

namespace SimplicialIso.Mixing

open Finset
open scoped InnerProductSpace

/-- (4.11), p. 18: for disjoint `A_0, …, A_d`, if `ρ` bounds the absolute value of every
eigenvalue of `αI − Δ⁺` on `Z_{d-1}`, then
`|⟨φ, (αI − Δ⁺) ℙ_{Z_{d-1}} ψ⟩| ≤ ρ √(|A_0| |A_d|) |A_1| ⋯ |A_{d-1}|`. -/
theorem eq_4_11 (n d : ℕ) (hd : 1 ≤ d) (X : Complex n d) (A : Fin (d + 1) → Finset (Fin n))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (α ρ : ℝ)
    (hρ : ∀ μ, IsCycleEigenvalue (α • LinearMap.id - upLap X) μ → |μ| ≤ ρ) :
    |⟪phi A, (α • LinearMap.id - upLap X : Form n d →ₗ[ℝ] Form n d) (projCycles n d (psi A))⟫_ℝ| ≤
      ρ * Real.sqrt (((A 0).card : ℝ) * (A (Fin.last d)).card) *
        ∏ i ∈ univ.filter (fun i : Fin (d + 1) => i ≠ 0 ∧ i ≠ Fin.last d),
          ((A i).card : ℝ) := by sorry

end SimplicialIso.Mixing
