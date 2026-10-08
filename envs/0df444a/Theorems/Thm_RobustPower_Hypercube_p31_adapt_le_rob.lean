-- Prove2me | Theorems.Thm_RobustPower_Hypercube_p31_adapt_le_rob
-- name    : RobustPower.Hypercube.p31_adapt_le_rob
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:05:45.163984+00:00
-- url     : https://prove2.me/theorems/b3db445f-a031-4716-8860-b02d64ba5b88
-- title:
--   p. 31 display — $z_{\mathrm{Adapt}}(A,B,b,d)\le z_{\mathrm{Rob}}(A,B,b,d)$
-- statement:
--   In the setting of (5.6)–(5.7), with $c\in\mathbb R^{n_1}_+$ and $d(\omega)\in\mathbb R^{n_2}_+$ for every scenario, the adaptive optimum never exceeds the robust optimum:
--
--   $$z_{\mathrm{Adapt}}(A,B,b,d)\le z_{\mathrm{Rob}}(A,B,b,d).$$
--
--   No assumption on the uncertainty set is needed. This is the first half of the proof of Theorem 5.4.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 31, proof of Theorem 5.4, first display

import Definitions.Def_RobustPower_Hypercube_Problems

namespace RobustPower.Hypercube

/-- First half of the proof of Theorem 5.4 (p. 31): a static solution `(x, y)` of
`Π_Rob(A,B,b,d)` used in every scenario is feasible for `Π_Adapt(A,B,b,d)` with the
same cost, so `z_Adapt(A,B,b,d) ≤ z_Rob(A,B,b,d)`. No assumption on the uncertainty set. -/
theorem p31_adapt_le_rob
    {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Ω → Matrix (Fin m) (Fin n₁) ℝ)
    (B : Ω → Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ)
    (hc : 0 ≤ c) (hd : ∀ ω, 0 ≤ d ω) :
    zAdapt A B b I₁ I₂ c d ≤ zRob A B b I₁ I₂ c d := by sorry

end RobustPower.Hypercube
