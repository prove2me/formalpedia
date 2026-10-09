-- Prove2me | Theorems.Thm_SimplicialIso_Mixing_eq_4_9
-- name    : SimplicialIso.Mixing.eq_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:30.211097+00:00
-- url     : https://prove2.me/theorems/a0b69695-7b31-49e4-b078-a959be8eb69d
-- title:
--   (4.9), p. 18 — for disjoint A_0,…,A_d, α⟨φ, ℙ_{B^{d−1}}ψ⟩ = α·|A_0|⋯|A_d|/n
-- statement:
--   Let $d\ge1$, let $A_0,\dots,A_d$ be pairwise disjoint sets of vertices among $n$, let $\varphi,\psi$ be as in (4.6), and let $\alpha\in\mathbb R$. Then
--   $$\alpha\langle\varphi,\mathbb P_{B^{d-1}}\psi\rangle=\frac{\alpha\cdot|A_0|\cdots|A_d|}{n}.\qquad(4.9)$$
--
--   It identifies the main term of (4.8) as the expected number of cells across the blocks.
--
--   **Formalization Note.** The left side does not involve the $d$-cells, so no complex appears. For $n=0$ both sides are $0$ (Lean's $x/0=0$ agrees, since there are no $(d-1)$-cells and every $A_i$ is empty).
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, §4.3, p. 18, equation (4.9)

import Mathlib
import Definitions.Def_SimplicialIso_Mixing_Setting
import Definitions.Def_SimplicialIso_Mixing_DeltaForms

namespace SimplicialIso.Mixing

open Finset
open scoped InnerProductSpace

/-- (4.9), p. 18: for disjoint `A_0, …, A_d` and every `α`,
`α ⟨φ, ℙ_{B^{d-1}} ψ⟩ = α · |A_0| ⋯ |A_d| / n`. -/
theorem eq_4_9 (n d : ℕ) (hd : 1 ≤ d) (A : Fin (d + 1) → Finset (Fin n))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (α : ℝ) :
    α * ⟪phi A, projExact n d (psi A)⟫_ℝ = α * (∏ i, ((A i).card : ℝ)) / n := by sorry

end SimplicialIso.Mixing
