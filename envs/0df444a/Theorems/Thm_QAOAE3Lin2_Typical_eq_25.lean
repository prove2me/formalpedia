-- Prove2me | Theorems.Thm_QAOAE3Lin2_Typical_eq_25
-- name    : QAOAE3Lin2.Typical.eq_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:48.224643+00:00
-- url     : https://prove2.me/theorems/fd40dfca-4e2a-407b-8ef7-8c41f29fc198
-- title:
--   Section II, (25), p. 6 — at β = π/4 the clause term ½d₁₂₃⟨Z₁Z₂Z₃⟩ equals ⅛d₁₂₃E_z[Σ sin(γ(d₁₂₃ ± c₁ ± c₂ ± c₃))]
-- statement:
--   Let the triples form an E3LIN2 family (each triple has three distinct bits, no triple repeated), take any right-hand sides, an equation $i$ with bits $1,2,3$ and sign $d_{123}$, and an angle $\gamma\in\mathbb R$. Let $c_1,c_2,c_3$ be the polynomials (21) collecting the equations that share exactly one bit with equation $i$. Then
--   $$\tfrac12 d_{123}\langle-\gamma,\pi/4|Z_1Z_2Z_3|-\gamma,\pi/4\rangle=\tfrac18 d_{123}\,\mathbb E_z\big[\sin(\gamma(d_{123}+c_1+c_2+c_3))+\sin(\gamma(d_{123}+c_1-c_2-c_3))+\sin(\gamma(d_{123}-c_1+c_2-c_3))+\sin(\gamma(d_{123}-c_1-c_2+c_3))\big].$$
--
--   This is the exact single-clause formula at $\beta=\pi/4$. It expresses a quantum expectation as a classical average over bit strings, and it shows that the clause term depends only on $d_{123}$ and on the signs of the equations sharing exactly one bit with equation $i$; equations sharing two bits with it drop out.
--
--   **Formalization Note** The left side is the summand of (55), i.e. the paper's (8) with $\beta=\pi/4$ and the state $|-\gamma,\pi/4\rangle$. $\mathbb E_z$ is the uniform average over all $2^n$ bit strings. The hypothesis that the triples are strictly increasing and pairwise distinct encodes "exactly 3 variables" and $d_{abc}\in\{0,\pm1\}$ of (6).
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 6, Section II, (25) (with (8), p. 4 and (19)–(21), p. 6)

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting

namespace QAOAE3Lin2.Typical

/-- (25), p. 6: at `β = π/4`, `½ d₁₂₃ ⟨−γ, π/4| Z₁Z₂Z₃ |−γ, π/4⟩` equals
`⅛ d₁₂₃ E_z[Σ sin(γ(d₁₂₃ ± c₁ ± c₂ ± c₃))]` over the four sign patterns. -/
theorem eq_25 {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (htri : QAOAE3Lin2.General.IsTripleFamily tri)
    (rhs : Fin m → Bool) (i : Fin m) (γ : ℝ) :
    clauseTerm tri rhs i γ = QAOAE3Lin2.General.clauseSin tri rhs i γ := by sorry

end QAOAE3Lin2.Typical
