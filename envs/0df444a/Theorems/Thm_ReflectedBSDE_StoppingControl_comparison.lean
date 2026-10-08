-- Prove2me | Theorems.Thm_ReflectedBSDE_StoppingControl_comparison
-- name    : ReflectedBSDE.StoppingControl.comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:14:08.005225+00:00
-- url     : https://prove2.me/theorems/34543db3-2322-4328-94d0-6b78844635d5
-- title:
--   Theorem 4.1 — comparison theorem for reflected BSDEs
-- statement:
--   Let $(\xi,f,S)$ and $(\xi',f',S')$ be two sets of data, each satisfying (i), (ii), (iv) and $S_T\le\xi$, $S'_T\le\xi'$ a.s., and suppose that at least one of $f$, $f'$ satisfies the Lipschitz condition (iii). Assume in addition
--
--   1. $\xi\le\xi'$ a.s.;
--   2. for every $(y,z)\in\mathbb R\times\mathbb R^d$, $f(t,y,z)\le f'(t,y,z)$ for $dP\times dt$-a.e. $(\omega,t)$;
--   3. $S_t\le S'_t$ for all $0\le t\le T$, a.s.
--
--   Let $(Y,Z,K)$ be a solution of the reflected BSDE with data $(\xi,f,S)$ and $(Y',Z',K')$ a solution of the reflected BSDE with data $(\xi',f',S')$. Then
--   $$Y_t\le Y'_t,\qquad 0\le t\le T,\quad\text{a.s.}$$
--
--   The comparison theorem gives the inequality $Y_t\le Y^{\beta,\gamma}_t$ for every admissible control, which is the first half of the minimax representation of Theorem 7.2.
--
--   **Formalization Note** "Solution" means a solution in the square-integrable class (v)–(viii) of `IsRBSDESolution`, as the proof (which uses Corollary 3.3) requires. The bracketed exception of the paper is stated as a disjunction: $f$ is Lipschitz or $f'$ is Lipschitz. Hypothesis 2 is read for each fixed $(y,z)$, as $P$-a.s. in $\omega$ and Lebesgue-a.e. in $t\in[0,T]$, not simultaneously for all $(y,z)$.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 712, Theorem 4.1, https://doi.org/10.1214/aop/1024404416

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MultiperiodRisk_Bellman_EssInf
import Definitions.Def_ReflectedBSDE_StoppingControl_Setting
import Definitions.Def_ReflectedBSDE_StoppingControl_Control

namespace ReflectedBSDE.StoppingControl

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Theorem 4.1 (El Karoui et al. 1997, p. 712), comparison theorem. Two sets of data
`(ξ, f, S)` and `(ξ', f', S')` each satisfy (i), (ii), (iv) and `S_T ≤ ξ`, at least one of
`f`, `f'` is Lipschitz (iii), and `ξ ≤ ξ'` a.s., `f(t, y, z) ≤ f'(t, y, z)` `dP × dt`-a.e. for
each `(y, z)`, `S_t ≤ S'_t` on `[0, T]` a.s. Then the solutions of the two reflected BSDEs
satisfy `Y_t ≤ Y'_t` for all `t ∈ [0, T]`, a.s. -/
theorem comparison {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : Peng1990.SMP.IsStdBrownian P B)
    (T : ℝ≥0) (ξ ξ' : Ω → ℝ) (f f' : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S S' : ℝ≥0 → Ω → ℝ)
    (hdata : StandingData (augFiltration hB) P T ξ f S)
    (hdata' : StandingData (augFiltration hB) P T ξ' f' S')
    (hLip : (∃ K : ℝ, IsLipschitzCoeff P T f K) ∨ (∃ K : ℝ, IsLipschitzCoeff P T f' K))
    (hξ : ∀ᵐ ω ∂P, ξ ω ≤ ξ' ω)
    (hf : ∀ (y : ℝ) (z : Fin d → ℝ), ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      f s.toNNReal ω y z ≤ f' s.toNNReal ω y z)
    (hS : ∀ᵐ ω ∂P, ∀ t ≤ T, S t ω ≤ S' t ω)
    (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
    (hsol : IsRBSDESolution (augFiltration hB) P T B ξ f S Y Z K)
    (Y' : ℝ≥0 → Ω → ℝ) (Z' : ℝ≥0 → Ω → Fin d → ℝ) (K' : ℝ≥0 → Ω → ℝ)
    (hsol' : IsRBSDESolution (augFiltration hB) P T B ξ' f' S' Y' Z' K') :
    ∀ᵐ ω ∂P, ∀ t ≤ T, Y t ω ≤ Y' t ω := by sorry

end ReflectedBSDE.StoppingControl
