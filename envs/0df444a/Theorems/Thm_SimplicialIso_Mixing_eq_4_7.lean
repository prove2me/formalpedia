-- Prove2me | Theorems.Thm_SimplicialIso_Mixing_eq_4_7
-- name    : SimplicialIso.Mixing.eq_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:20.98101+00:00
-- url     : https://prove2.me/theorems/432df7ab-4858-4252-9763-7a40bc491ea0
-- title:
--   (4.7), p. 17 — for disjoint A_0,…,A_d and every α ∈ ℝ, ⟨φ, (D − Δ⁺)ψ⟩ = ⟨φ, (αI − Δ⁺)ψ⟩
-- statement:
--   Let $X$, $d\ge1$, the pairwise disjoint sets $A_0,\dots,A_d$ and $\varphi,\psi$ be as in (4.6). Since the $A_i$ are disjoint, $\varphi$ and $\psi$ are supported on different $(d-1)$-cells, so for every $\alpha\in\mathbb R$
--   $$\langle\varphi,(D-\Delta^+)\psi\rangle=\langle\varphi,-\Delta^+\psi\rangle=\langle\varphi,(\alpha I-\Delta^+)\psi\rangle.\qquad(4.7)$$
--
--   It frees the parameter $\alpha$ that appears in the Mixing Lemma.
--
--   **Formalization Note.** The Lean statement asserts the equality of the outer two expressions.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, §4.3, p. 17, equation (4.7)

import Mathlib
import Definitions.Def_SimplicialIso_Mixing_Setting
import Definitions.Def_SimplicialIso_Mixing_DeltaForms

namespace SimplicialIso.Mixing

open Finset
open scoped InnerProductSpace

/-- (4.7), p. 17: for disjoint `A_0, …, A_d` and every `α`,
`⟨φ, (D − Δ⁺) ψ⟩ = ⟨φ, (αI − Δ⁺) ψ⟩`. -/
theorem eq_4_7 (n d : ℕ) (hd : 1 ≤ d) (X : Complex n d) (A : Fin (d + 1) → Finset (Fin n))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (α : ℝ) :
    ⟪phi A, (degOp X - upLap X) (psi A)⟫_ℝ =
      ⟪phi A, (α • LinearMap.id - upLap X : Form n d →ₗ[ℝ] Form n d) (psi A)⟫_ℝ := by sorry

end SimplicialIso.Mixing
