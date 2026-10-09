-- Prove2me | Theorems.Thm_PhaseCut_Tight_phaseCut_optimal_mem_phaseCutModFeasible
-- name    : PhaseCut.Tight.phaseCut_optimal_mem_phaseCutModFeasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:39:24.173013+00:00
-- url     : https://prove2.me/theorems/c75643dd-b3b4-460b-8bf8-0210a5d7bdcf
-- title:
--   §4.3, p. 12 — when (1) is solvable, every optimal solution of PhaseCut is feasible for PhaseCutMod
-- statement:
--   Let $A\in\mathbb C^{n\times p}$ be injective, let $b\in\mathbb R^n$, and assume problem (1) is solvable: there is $x\in\mathbb C^p$ with $|Ax|=b$. Let $M=\operatorname{diag}(b)(\mathbf I-AA^\dagger)\operatorname{diag}(b)$. Then every optimal solution $U$ of
--
--   $$\text{(PhaseCut)}\qquad \min\ \operatorname{Tr}(UM)\quad\text{s.t.}\quad \operatorname{diag}(U)=1,\ U\succeq 0$$
--
--   is a feasible point of PhaseCutMod, i.e. it also satisfies $\operatorname{Tr}(MU)=0$.
--
--   This justifies PhaseCutMod as a refinement of PhaseCut: in the noiseless case it selects, among the optimal points of PhaseCut, one of minimal $\operatorname{Tr}(BU)$.
--
--   **Formalization Note** Injectivity of $A$ is not in the page's sentence; it is added because $A^\dagger$ is encoded as $(A^*A)^{-1}A^*$, which is the pseudoinverse only for injective $A$, and it is the standing assumption of this mission. The PhaseCut objective is the real part of $\operatorname{Tr}(UM)$.
-- source:
--   Waldspurger, d'Aspremont & Mallat, arXiv:1206.0102v3, §4.3, p. 12 (sentence after (PhaseCutMod))

import Mathlib
import Definitions.Def_PhaseCut_Tight_Defs

namespace PhaseCut.Tight

open Matrix
open scoped ComplexOrder

/-- §4.3, p. 12: when (1) is solvable (and `A` is injective, so that `pinv A` is `A†`), every optimal
solution of PhaseCut is a feasible point of PhaseCutMod. -/
theorem phaseCut_optimal_mem_phaseCutModFeasible {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ)
    (b : Fin n → ℝ) (hA : Function.Injective A.mulVec) (hsol : IsSolvable A b) :
    ∀ U ∈ phaseCutOptimal A b, U ∈ phaseCutModFeasible A b := by sorry

end PhaseCut.Tight
