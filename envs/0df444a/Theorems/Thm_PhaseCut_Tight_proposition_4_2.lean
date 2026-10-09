-- Prove2me | Theorems.Thm_PhaseCut_Tight_proposition_4_2
-- name    : PhaseCut.Tight.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:39:04.424317+00:00
-- url     : https://prove2.me/theorems/b4a9d0c9-c4c0-43f0-a9db-824eef215bc4
-- title:
--   Proposition 4.2, p. 12 — Φ(X) = diag(b)⁻¹AXA*diag(b)⁻¹ is a bijection from the PhaseLift feasible set onto the PhaseCutMod feasible set
-- statement:
--   Let $A\in\mathbb C^{n\times p}$ and $b\in\mathbb R^n$. Assume that
--
--   1. $b_i\neq 0$ for $i=1,\dots,n$;
--   2. $A$ is injective;
--   3. problem (1) has a solution, i.e. there is $x\in\mathbb C^p$ with $|Ax|=b$.
--
--   Then the map
--
--   $$\Phi:\mathbf H_p\to\mathbf H_n,\qquad \Phi(X)=\operatorname{diag}(b)^{-1}AXA^*\operatorname{diag}(b)^{-1}$$
--
--   is a bijection from the feasible set of PhaseLift, $\{X\succeq 0 : \operatorname{Tr}(a_ia_i^*X)=b_i^2,\ i=1,\dots,n\}$, onto the feasible set of PhaseCutMod, $\{U\succeq 0 : \operatorname{diag}(U)=1,\ \operatorname{Tr}(MU)=0\}$, where $M=\operatorname{diag}(b)(\mathbf I-AA^\dagger)\operatorname{diag}(b)$.
--
--   This bijection is the core of the equivalence between PhaseLift and the modified MaxCut-type relaxation PhaseCutMod: combined with the fact that $\Phi$ preserves the trace objective and the rank, it transfers tightness from PhaseLift to PhaseCutMod (Corollary 4.3).
--
--   **Formalization Note** "A bijection between the feasible points of PhaseCutMod and those of PhaseLift" is stated as `Set.BijOn Φ (PhaseLift feasible) (PhaseCutMod feasible)`: $\Phi$ maps the first set into the second, injectively, and onto it. $\Phi$ is defined on all $p\times p$ complex matrices.
-- source:
--   Waldspurger, d'Aspremont & Mallat, arXiv:1206.0102v3, Proposition 4.2, p. 12

import Mathlib
import Definitions.Def_PhaseCut_Tight_Defs

namespace PhaseCut.Tight

open Matrix
open scoped ComplexOrder

/-- Proposition 4.2, p. 12: if `bᵢ ≠ 0` for all `i`, `A` is injective and (1) has a solution, then
`Φ(X) = diag(b)⁻¹AXA*diag(b)⁻¹` maps the feasible set of PhaseLift bijectively onto the feasible
set of PhaseCutMod. -/
theorem proposition_4_2 {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ)
    (hb : ∀ i, b i ≠ 0) (hA : Function.Injective A.mulVec) (hsol : IsSolvable A b) :
    Set.BijOn (Phi A b) (phaseLiftFeasible A b) (phaseCutModFeasible A b) := by sorry

end PhaseCut.Tight
