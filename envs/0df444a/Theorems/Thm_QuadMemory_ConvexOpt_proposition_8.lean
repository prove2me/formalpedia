-- Prove2me | Theorems.Thm_QuadMemory_ConvexOpt_proposition_8
-- name    : QuadMemory.ConvexOpt.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:45.081991+00:00
-- url     : https://prove2.me/theorems/25a890dd-891d-4f57-ac55-6e3d90077b07
-- title:
--   Proposition 8, p. 12 — with probability ≥ 1 − C√(log d)/d², Procedure 1 answers as a first-order oracle of F_{A,v,P,L}
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Let $1\le k\le d/3-1$ with $p_{max}\ge1$, let the cells of $\mathcal D_\delta$ have diameter at most $1/d^3$, let $A\in\{\pm1\}^{n\times d}$ and $v_0\in\mathcal D_\delta$. For any algorithm, on an event $\mathcal E$ of probability at least
--   $$1-\frac{C\sqrt{\log d}}{d^2}$$
--   on the randomness of the procedure, all responses of the optimization procedure are consistent with a first-order oracle for $F_{A,v,P,L}$: for every $t\ge1$, if $(f_t,g_t)$ is the response at time $t$ to the query $x_t$, then $f_t=F_{A,v,P,L}(x_t)$ and $g_t=\partial F_{A,v,P,L}(x_t)$.
--
--   Although the procedure builds its function while the algorithm runs, the algorithm cannot tell it apart from a fixed convex function, so any optimizer of convex functions also optimizes the procedure.
--
--   **Formalization Note.** "On the randomness of the procedure" with $A$ and $v_0$ fixed is the conditional probability given $A$ and the cell of $v_0$, written as a weighted sum over the hint cells with $v_0$'s cell fixed. The binder $0<d$ only names the first hint; it follows from $1\le k\le d/3-1$.
-- source:
--   Blanchard, Zhang & Jaillet, arXiv:2302.04963v2, p. 12, Proposition 8 (proof pp. 12–14)

import Mathlib
import Definitions.Def_QuadMemory_ConvexOpt_Model
import Definitions.Def_QuadMemory_ConvexOpt_Game
import Definitions.Def_QuadMemory_ConvexOpt_Procedure

open scoped ENNReal

namespace QuadMemory.ConvexOpt

/-- Proposition 8 (p. 12): there is a universal `C > 0` such that, for every `A` and every `v_0`
(cell `i₀` of the first hint), on an event of conditional probability at least
`1 - C √(log d)/d²` over the randomness of the procedure, every response of Procedure 1 is that of
a first-order oracle for `F_{A,v,P,L}`: `f_t = F_{A,v,P,L}(x_t)` and `g_t = ∂F_{A,v,P,L}(x_t)` for all
`t ≥ 1`. -/
theorem proposition_8 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d k M : ℕ) (hd : 0 < d), 1 ≤ k → (k : ℝ) ≤ (d : ℝ) / 3 - 1 →
      1 ≤ pmax d k → ∀ (D : SphereDisc d), D.DiamLe (1 / (d : ℝ) ^ 3) →
      ∀ (alg : MemAlg d M) (A : SignMatrix d) (i₀ : D.ι),
        ENNReal.ofReal (1 - C * Real.sqrt (Real.log d) / (d : ℝ) ^ 2) *
            (∑ w : Fin d → D.ι, if w ⟨0, hd⟩ = i₀ then procWeight alg k D A w else 0) ≤
          ∑ w : Fin d → D.ι,
            open Classical in
            if w ⟨0, hd⟩ = i₀ ∧ ∀ t : ℕ, 1 ≤ t →
                procResp alg k D A w t =
                  (Ffinal alg k D A w (procQuery alg k D A w t),
                    subgradFfinal alg k D A w (procQuery alg k D A w t))
            then procWeight alg k D A w else 0 := by sorry

end QuadMemory.ConvexOpt
