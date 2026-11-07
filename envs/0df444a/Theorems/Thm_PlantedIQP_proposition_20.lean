-- Prove2me | Theorems.Thm_PlantedIQP_proposition_20
-- name    : PlantedIQP.proposition_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:46.777675+00:00
-- url     : https://prove2.me/theorems/1d79b83d-a371-42f1-b245-b27e35beebe9
-- title:
--   Proposition 20 — $V$ is an independent space iff $T_g|_{V^3}\equiv0$ iff $\deg(g|_V)\le2$
-- statement:
--   Let $g$ be a cubic polynomial and $V\le\mathbb F_2^n$. The following are equivalent:
--
--   1. $V$ is an independent space of $g$ (Definition 1);
--   2. $T_g(u,v,w)=0$ for all $u,v,w\in V$;
--   3. $\deg(g|_V)\le2$: for every basis $b_1,\dots,b_d$ of $V$, the multilinear representative of $y\mapsto g\big(\sum_iy_ib_i\big)$ has degree at most $2$.
--
--   This characterization makes independent spaces a property of the subspace alone, independent of the matrix $A$ in Definition 1.
--
--   Differences from the source:
--   - reading: deg(g|_V) ≤ 2 → for every basis b of V, the multilinear representative of y ↦ g(Σᵢ yᵢ bᵢ) has degree ≤ 2; reason: the source fixes no basis; the degree does not depend on it, and the every-basis form implies the some-basis form since V has a basis
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Proposition 20, p.16

import Mathlib
import Definitions.Def_PlantedIQP_IsIndependentSpace
import Definitions.Def_PlantedIQP_triForm

set_option autoImplicit false

namespace PlantedIQP

/-- Bläser, Gullans, Hangleiter, Liu, Qiao, *Verifiable quantum advantage based on polynomials with
planted structures*, arXiv:2609.39918 (sha256 6e261694…), Proposition 20, p.16: for a cubic polynomial `g` and `V ≤ 𝔽₂ⁿ`, `V` is an
independent space of `g` (Definition 1) iff `T_g|_{V³} ≡ 0`, equivalently `deg(g|_V) ≤ 2`, where
`g|_V` is `y ↦ g(Σ_i y_i b_i)` for a basis `b` of `V` (for every basis). -/
theorem proposition_20 {n : ℕ} (g : CubicPoly n) (V : Submodule (ZMod 2) (Vec n)) :
    (IsIndependentSpace g V ↔ ∀ u ∈ V, ∀ v ∈ V, ∀ w ∈ V, triForm g u v w = 0) ∧
      ((∀ u ∈ V, ∀ v ∈ V, ∀ w ∈ V, triForm g u v w = 0) ↔
        ∀ (d : ℕ) (b : Fin d → Vec n), LinearIndependent (ZMod 2) b →
          Submodule.span (ZMod 2) (Set.range b) = V →
            DegLE (fun y : Fin d → ZMod 2 => g.eval (∑ i, y i • b i)) 2) := by sorry

end PlantedIQP
