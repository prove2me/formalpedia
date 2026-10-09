-- Prove2me | Theorems.Thm_SimplicialIso_Mixing_eq_4_6
-- name    : SimplicialIso.Mixing.eq_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:28.081989+00:00
-- url     : https://prove2.me/theorems/4c65b9ec-8042-42ea-83be-52f89f9a6fcc
-- title:
--   (4.6), p. 17 — for disjoint A_0,…,A_d, ⟨φ, (D − Δ⁺)ψ⟩ = |F(A_0,…,A_d)|
-- statement:
--   Let $X$ be a $d$-dimensional complex with a complete skeleton on $n$ vertices, $d\ge1$, let $A_0,\dots,A_d$ be pairwise disjoint sets of vertices (not necessarily a partition), and let $\varphi=\delta_{A_0,A_1,\dots,A_{d-1}}$, $\psi=\delta_{A_d,A_1,\dots,A_{d-1}}$. With the degree operator $(Df)(\sigma)=\deg(\sigma)f(\sigma)$,
--   $$\langle\varphi,(D-\Delta^+)\psi\rangle=|F(A_0,A_1,\dots,A_d)|.\qquad(4.6)$$
--
--   This is the identity that expresses the number of $d$-cells meeting every $A_i$ through the upper Laplacian.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, §4.3, p. 17, equation (4.6)

import Mathlib
import Definitions.Def_SimplicialIso_Mixing_Setting
import Definitions.Def_SimplicialIso_Mixing_DeltaForms

namespace SimplicialIso.Mixing

open Finset
open scoped InnerProductSpace

/-- (4.6), p. 17: for disjoint `A_0, …, A_d`, `⟨φ, (D − Δ⁺) ψ⟩ = |F(A_0, …, A_d)|`. -/
theorem eq_4_6 (n d : ℕ) (hd : 1 ≤ d) (X : Complex n d) (A : Fin (d + 1) → Finset (Fin n))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ⟪phi A, (degOp X - upLap X) (psi A)⟫_ℝ = ((F X A).card : ℝ) := by sorry

end SimplicialIso.Mixing
