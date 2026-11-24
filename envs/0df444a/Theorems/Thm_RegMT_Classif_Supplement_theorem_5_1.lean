-- Prove2me | Theorems.Thm_RegMT_Classif_Supplement_theorem_5_1
-- name    : RegMT.Classif.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:36:43.768441+00:00
-- url     : https://prove2.me/theorems/c3db115b-fc5a-4041-8aba-bcf58cb1baa6
-- title:
--   Theorem 5.1 — absolute error extrema
-- statement:
--   Use $N\ge1$ samples, the full finite-dimensional input-output space, an arbitrary joint norm and any $\rho\ge0$. For a fixed linear hypothesis $w$ set $r_w(x,y)=\langle w,x\rangle-y$, and let $A=N^{-1}\sum_i|r_w(\hat\xi_i)|$. Then both extremal expected absolute errors are
--   $$\sup_{Q\in B_\rho(\hat P_N)}\mathbb E_Q|r_w(\xi)|=A+\rho\|r_w\|_*,$$
--   $$\inf_{Q\in B_\rho(\hat P_N)}\mathbb E_Q|r_w(\xi)|=\max\{A-\rho\|r_w\|_*,0\}.$$
--   Here $\|r_w\|_*=\|(w,-1)\|_*$ is computed for the same arbitrary joint norm as the transport cost. Both clauses include radius zero. The lower truncation in the best-case identity is retained, and expectations are extended nonnegative integrals.
--
--   Differences from the source:
--   - encoding: Finite Euclidean coordinates, ordinary expectations and mathematical optimization notation. → Coordinate-free normed spaces or real Hilbert spaces, extended nonnegative integrals and guarded extended extrema, with all sample and piece ranges explicit.; reason: These representations preserve the source domain, arbitrary norms, exact constants, and infinite values; nonnegative loss and measurable probability spaces are the standing conventions.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p. 22, Theorem 5.1; Appendix A proof

import Mathlib
import Definitions.Def_RegMT_Classif_Supplement_Perturbation

open scoped ENNReal

namespace RegMT.Classif.Supplement

theorem theorem_5_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n N : ℕ}
    (e : E ≃L[ℝ] (Fin n → ℝ) × ℝ) (hN : 0 < N) (z : Fin N → E) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (w : Fin n → ℝ) :
    normRisk Set.univ z ρ (fun ξ => |RegMT.Regress.pairing e w ξ|) =
      ENNReal.ofReal (empiricalAbs z (RegMT.Regress.pairing e w) + ρ * ‖RegMT.Regress.pairing e w‖) ∧
    bestAbs z ρ (RegMT.Regress.pairing e w) =
      ENNReal.ofReal (max (empiricalAbs z (RegMT.Regress.pairing e w) -
        ρ * ‖RegMT.Regress.pairing e w‖) 0) := by sorry

end RegMT.Classif.Supplement
