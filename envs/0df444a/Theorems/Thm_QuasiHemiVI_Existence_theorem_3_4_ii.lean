-- Prove2me | Theorems.Thm_QuasiHemiVI_Existence_theorem_3_4_ii
-- name    : QuasiHemiVI.Existence.theorem_3_4_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:35:29.350746+00:00
-- url     : https://prove2.me/theorems/b38fc904-204e-4afd-9cc7-d1c92bbbffc7
-- title:
--   Theorem 3.4 (ii) — $\mathrm{SOL}(C;T,J,\varphi,f)$ is nonempty, bounded and weakly closed
-- statement:
--   Let $V$ be a real reflexive Banach space and $X$, $Y$ real Banach spaces. Assume (HC), (HJ), (Hγ), (H0), (HT), (Hφ) and the coercivity condition (3.2) (with a bounded set $C_0$ meeting $C$). Then the solution set of the generalized hemivariational inequality Problem 3.3,
--
--   $$
--   \mathrm{SOL}(C;T,J,\varphi,f)=\{u\in C:\ \exists\,u^*\in T(u)\ \forall v\in C,\ \langle u^*,v-u\rangle+\varphi(v,u)+J^0(\gamma u;\gamma(v-u))\ge\langle f,\pi(v-u)\rangle\},
--   $$
--
--   is nonempty, bounded, and weakly closed in $V$.
--
--   Applied with $C$ replaced by $K(w)$, this result gives that each value $S(w)$ of the variational selection is nonempty, which is the first step towards the existence theorem for the quasi-hemivariational inequality.
--
--   **Formalization Note** "Weakly closed" is stated as sequential weak closedness; for the bounded set $\mathrm{SOL}$ in the reflexive space $V$ this is equivalent to weak closedness (Eberlein–Šmulian).
-- source:
--   Zeng, Migórski & Khan, Nonlinear Quasi-hemivariational Inequalities: Existence and Optimal Control, SIAM J. Control Optim. 59(2) (2021) 1246–1274, doi:10.1137/19M1282210, p. 1251, Theorem 3.4 (ii)

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_ClarkeDeriv
import Definitions.Def_QuasiHemiVI_Existence_WeakConv
import Definitions.Def_QuasiHemiVI_Existence_SetValued
import Definitions.Def_QuasiHemiVI_Existence_Hypotheses
import Definitions.Def_QuasiHemiVI_Existence_Problems

namespace QuasiHemiVI.Existence

/-- Theorem 3.4 (ii), p. 1251: under (HC), (HJ), (Hγ), (H0), (HT), (Hφ) and (3.2), the solution
set `SOL(C; T, J, φ, f)` of Problem 3.3 is nonempty, bounded and (sequentially) weakly closed in `V`. -/
theorem theorem_3_4_ii {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (hV : IsReflexive V)
    (C : Set V) (T : V → Set (V →L[ℝ] ℝ)) (φ : V → V → ℝ) (J : X → ℝ)
    (γ : V →L[ℝ] X) (π : V →L[ℝ] Y) (f : Y →L[ℝ] ℝ) (h : V → ℝ) (C₀ : Set V)
    (hC : HC C) (hJ : LocallyLipschitz J) (hT : HT C T φ J γ π f h) (hφ : Hphi φ)
    (h32 : Coercive32 C T φ J γ C₀) :
    (SOL C T φ J γ π f).Nonempty ∧ Bornology.IsBounded (SOL C T φ J γ π f) ∧
      IsSeqWeaklyClosed (SOL C T φ J γ π f) := by sorry

end QuasiHemiVI.Existence
