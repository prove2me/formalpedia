-- Prove2me | Theorems.Thm_PrideGuilt_proposition_1
-- name    : PrideGuilt.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:01:44.89988+00:00
-- url     : https://prove2.me/theorems/9387e5fa-cf04-4cfe-8cf8-8b6302d32285
-- title:
--   Proposition 1 — remanufacturing at reward $f$ beats the benchmark iff $g(f)>0$ (corrected: demand $D\ge0$)
-- statement:
--   Assume the standing assumptions, $\gamma_P>0$, $\gamma_G>0$, $\gamma_P\ne\gamma_G$. For a reward $f\le c_r$ let $\Pi^\star(f)$ be the best profit over prices with nonnegative demand. Then
--
--   $$
--   \Pi^\star(f)>\Pi_0 \iff g(f)>0,\qquad g(f)=\frac{b_1}{b_0}\big(\bar U(f)+I_G\big)+\tau^*(f)(\Delta c-f),
--   $$
--
--   where $\Pi_0$ is the benchmark profit without remanufacturing.
--
--   The proposition reduces the decision to remanufacture at a given reward to the sign of the explicit function $g$.
--
--   Differences from the source:
--   - correction: Π⋆(f) ≡ max_p Π(p, f), unconstrained → Π⋆(f) is the supremum of Π(p, f) over prices with D(p, f) ≥ 0; reason: as printed the statement is false: b0 = 1, b1 = 0, IG = IP = 0, cn = 1, cu = 0.5, ce = 3, γP = 2, γG = 1, f = 3 ≤ c_r give τ*(3) = 1 and g(3) = −2.5, yet max_p (1 − p)(p − 3.5) = 1.5625 > 0 = Π_0, at a price with demand −1.25
--   - encoding: Π_0, the benchmark optimum of (7) → supremum of Π̃ over prices with D̃(p) ≥ 0; reason: the constraint does not bind under 1 − b1IG − b0cn ≥ 0, so the value is that of (7)
--   - encoding: τ*(f), the evolutionarily stable rate of Lemma 1 → the Lemma 1 formula tauStar, including its printed values at the endpoints and at τ^0 = τ_m(f); reason: the manufacturer's problem is built on the Lemma 1 formula (p.11); the equivalence holds whatever value τ* takes at those points, since Π⋆(f) − Π_0 has the sign of g(f) for any value of τ*(f)
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Proposition 1 and eq. (8), p.12

import Mathlib
import Definitions.Def_PrideGuilt_Standing
import Definitions.Def_PrideGuilt_innerOpt
import Definitions.Def_PrideGuilt_benchOpt
import Definitions.Def_PrideGuilt_gFun

namespace PrideGuilt

/-- **Proposition 1 (when remanufacturing beats the benchmark), corrected: demand `D ≥ 0`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Proposition 1 and eq. (8), p.12 (PDF 13).

Under the standing assumptions, with `γ_P, γ_G > 0` and `γ_P ≠ γ_G`, for every reward
`f ≤ c_r`: `Π⋆(f) > Π₀` iff `g(f) > 0`, where `Π⋆(f)` is the supremum of `Π(p, f)` over the prices
with `D(p, f) ≥ 0` and `g(f) = (b₁/b₀)(Ū(f) + I_G) + τ*(f)(Δc − f)`.

**Formalization Note.** As printed (unconstrained `max_p`) the statement is false: `b₀ = 1`,
`b₁ = 0`, `I_G = I_P = 0`, `c_n = 1`, `c_u = 0.5`, `c_e = 3`, `γ_P = 2`, `γ_G = 1`, `f = 3` give
`g(3) = −2.5` but `max_p (1 − p)(p − 3.5) = 1.5625 > 0 = Π₀`, at a price with demand `−1.25`. -/
theorem proposition_1 (P : Params) (hP : Standing P) (γP γG : ℝ) (hγP : 0 < γP) (hγG : 0 < γG)
    (hne : γP ≠ γG) (f : ℝ) (hf : f ≤ cr P) :
    benchOpt P < innerOpt P γP γG f ↔ 0 < gFun P γP γG f := by sorry

end PrideGuilt
