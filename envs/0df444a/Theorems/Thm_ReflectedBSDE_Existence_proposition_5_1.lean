-- Prove2me | Theorems.Thm_ReflectedBSDE_Existence_proposition_5_1
-- name    : ReflectedBSDE.Existence.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:31.912555+00:00
-- url     : https://prove2.me/theorems/f461d53e-234d-47d8-80ae-94d6d1ec0c10
-- title:
--   Proposition 5.1 — the backward reflection problem ($f$ independent of $(y,z)$) has a unique solution
-- statement:
--   Suppose that the coefficient does not depend on $(y,z)$: $f=f(t)$ is a given $\mathcal F_t$-progressively measurable process with
--   $$\text{(ii}'\text{)}\qquad E\int_0^Tf(t)^2\,dt<\infty.$$
--   Let $\xi$ satisfy (i), let $S$ satisfy (iv), and let $S_T\le\xi$ almost surely. A solution of the **backward reflection problem (BRP)** is a triple $(Y,Z,K)$ satisfying (v), (vii), (viii) and
--   $$\text{(vi}'\text{)}\qquad Y_t=\xi+\int_t^Tf(s)\,ds+K_T-K_t-\int_t^T(Z_s,dB_s),\qquad 0\le t\le T.$$
--   Then the BRP has a solution, and any two solutions coincide: the $Y$'s and $K$'s are indistinguishable on $[0,T]$, and the $Z$'s agree $dP\otimes dt$-almost everywhere.
--
--   The BRP is the linear building block of the existence proof. Theorem 5.2 obtains the solution of the general reflected BSDE as a fixed point of the map that sends $(U,V)$ to the solution of the BRP with coefficient $f(s,U_s,V_s)$.
--
--   **Formalization Note** The BRP is the reflected BSDE of `ReflectedBSDE.Existence.Solution` with the coefficient $(t,\omega,y,z)\mapsto f(t,\omega)$, so no separate definition is introduced. The paper's "(ii)" in the statement of Proposition 5.1 is (ii′), and no Lipschitz condition is needed.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 716 (PDF p. 15), (ii′), (vi′) and Proposition 5.1

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Skorohod
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_ReflectedBSDE_Existence_Solution

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Peng1990.SMP

namespace ReflectedBSDE.Existence

/-- Proposition 5.1 (p. 716): if the coefficient `f(t)` does not depend on `(y, z)` and is a
progressively measurable process with (ii′) `E ∫₀ᵀ f(t)² dt < ∞`, then under (i), (iv) and
`S_T ≤ ξ` the backward reflection problem (v), (vi′), (vii), (viii) has a unique solution. -/
theorem proposition_5_1 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : IsStdBrownian P B)
    (T : ℝ≥0) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (hξ : IsTerminalValue (augmentedFiltration P hB) P T ξ)
    (hf : L2F (augmentedFiltration P hB) P T f)
    (hS : IsObstacle (augmentedFiltration P hB) P T S)
    (hST : ∀ᵐ ω ∂P, S T ω ≤ ξ ω) :
    (∃ (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ),
        SatisfiesV (augmentedFiltration P hB) P T Z ∧
        SolvesRBSDE (augmentedFiltration P hB) P T B ξ (fun t ω _ _ => f t ω) S Y Z K) ∧
    ∀ (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
      (Y' : ℝ≥0 → Ω → ℝ) (Z' : ℝ≥0 → Ω → Fin d → ℝ) (K' : ℝ≥0 → Ω → ℝ),
      SatisfiesV (augmentedFiltration P hB) P T Z →
      SolvesRBSDE (augmentedFiltration P hB) P T B ξ (fun t ω _ _ => f t ω) S Y Z K →
      SatisfiesV (augmentedFiltration P hB) P T Z' →
      SolvesRBSDE (augmentedFiltration P hB) P T B ξ (fun t ω _ _ => f t ω) S Y' Z' K' →
      SameSolution P T Y Z K Y' Z' K' := by sorry

end ReflectedBSDE.Existence
