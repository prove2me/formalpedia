-- Prove2me | Theorems.Thm_QAOAE3Lin2_General_eq_25
-- name    : QAOAE3Lin2.General.eq_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:24.710462+00:00
-- url     : https://prove2.me/theorems/c0105915-ae21-4840-8858-3852981045ce
-- title:
--   Section II, (25), p. 6 — at β = π/4 the clause term ½d⟨Z₁Z₂Z₃⟩ at −γ equals ⅛dE_z[Σ sin(γ(d ± c₁ ± c₂ ± c₃))]
-- statement:
--   Let an instance of Max E3LIN2 be given in which every equation is on three distinct bits and no triple carries two equations. Fix an equation with sign $d$ and bits $1,2,3$, and let $c_1,c_2,c_3$ be its polynomials (21). Then for every real $\gamma$,
--   $$\tfrac12 d\,\langle-\gamma,\tfrac\pi4|Z_1Z_2Z_3|-\gamma,\tfrac\pi4\rangle=\tfrac18 d\,E_z\big[\sin(\gamma(d+c_1+c_2+c_3))+\sin(\gamma(d+c_1-c_2-c_3))+\sin(\gamma(d-c_1+c_2-c_3))+\sin(\gamma(d-c_1-c_2+c_3))\big].$$
--
--   This exact single-clause formula is the starting point of both the worst-case analysis (Taylor expansion in $\gamma$) and the typical-case analysis.
--
--   **Formalization Note.** The left side is the paper's (8) at $\beta=\pi/4$, i.e. $\tfrac12d\langle s|e^{-i\gamma C}e^{i\beta B}Z_1Z_2Z_3e^{-i\beta B}e^{i\gamma C}|s\rangle$, the state at angle $-\gamma$. The triple condition is needed: a second equation on the same triple would change the commutation step (11).
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 6, Section II, (25) (with (8), p. 4, and (21), p. 6)

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting

namespace QAOAE3Lin2.General

theorem eq_25 {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (htri : IsTripleFamily tri) (i : Fin m) (γ : ℝ) :
    (1 / 2) * sgn rhs i * corr tri rhs i (-γ) (Real.pi / 4) = clauseSin tri rhs i γ := by sorry

end QAOAE3Lin2.General
