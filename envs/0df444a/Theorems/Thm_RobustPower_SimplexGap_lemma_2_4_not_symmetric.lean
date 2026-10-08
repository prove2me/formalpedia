-- Prove2me | Theorems.Thm_RobustPower_SimplexGap_lemma_2_4_not_symmetric
-- name    : RobustPower.SimplexGap.lemma_2_4_not_symmetric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:23:03.534583+00:00
-- url     : https://prove2.me/theorems/fe1887f2-f136-4c22-873a-6c1ca6c2ef07
-- title:
--   Lemma 2.4 — the corner simplex is not symmetric for n ≥ 2
-- statement:
--   Let $n\ge 2$ and let
--   $$\Delta_n=\Big\{\,b\in\mathbb R^n \;:\; \sum_{j=1}^n b_j\le 1,\ b\ge 0\,\Big\}$$
--   be the uncertainty set (2.29). Then $\Delta_n$ is not symmetric: there is no point $u^0\in\Delta_n$ such that $u^0+z\in\Delta_n\iff u^0-z\in\Delta_n$ for all $z\in\mathbb R^n$.
--
--   This is what makes Theorem 2.6 an example outside the scope of the paper's symmetric bound $z_{\mathrm{Rob}}(b)\le 2\,z_{\mathrm{Stoch}}(b)$: the simplex violates exactly the symmetry hypothesis. For $n=1$ the set $[0,1]$ is symmetric about $1/2$, so $n\ge 2$ is needed.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 19, Lemma 2.4

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets
import Definitions.Def_RobustPower_SimplexGap_SimplexInstance

namespace RobustPower.SimplexGap

/-- Lemma 2.4: the corner simplex (2.29) is not symmetric (Definition 1.2) for `n ≥ 2`. -/
theorem lemma_2_4_not_symmetric (n : ℕ) (hn : 2 ≤ n) :
    ¬ RobustPower.StochGap.IsSymmetric (cornerSimplex n) := by sorry

end RobustPower.SimplexGap
