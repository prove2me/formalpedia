-- Prove2me | Theorems.Thm_UltrametricFit_integer_point
-- name    : UltrametricFit.integer_point
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:34.613042+00:00
-- url     : https://prove2.me/theorems/98c1b8af-0d86-47de-aab9-14b0b60ad610
-- title:
--   §2, pp.6–7 — integer points of the LP
-- statement:
--   Let $U$ be an ultrametric with $U(i,j)\in\{D_1,\dots,D_L\}$ for $i\ne j$, $p\ge1$, and define $x_\ell(i,j)=1$ when $U(i,j)>D_\ell$ and $x_\ell(i,j)=0$ otherwise (with $x_0=1$ on pairs and $x_\ell(i,i)=0$). Then $x$ is feasible for the LP and
--   $$\mathrm{lp\text{-}cost}_p(x)=\|U-X\|_p^p.$$
--   So the optimal LP value is at most $\|U-X\|_p^p$ for every such $U$, which is the sense in which the LP relaxes the fitting problem.
--
--   Differences from the source:
--   - encoding: $X, U, x_\ell$ are functions on unordered pairs → symmetric functions on `Fin n × Fin n`, with sums over $i<j$ and diagonals never read; reason: Lean convention; same instances
--   - reading: the page describes the integer program's indicator variables and derives the constraints in prose, and calls the LP a relaxation → the indicator point is feasible and its LP objective equals $\|U-X\|_p^p$; reason: this is the content of being a relaxation, and the proof of Theorem 1 uses it together with Lemma 4
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), §2, pp.6–7; used in the proof of Theorem 1, p.15

import Mathlib
import Definitions.Def_UltrametricFit_IsInstance
import Definitions.Def_UltrametricFit_IsFeasible

namespace UltrametricFit

/-- **The integer points of the LP**, Charikar, Gao, STOC 2027 submission (manuscript sha256
87af12a2…), §2, pp.6–7: the indicator `x_ℓ(i, j)` of `U(i, j) > D_ℓ` of an ultrametric `U` with values
in `{D_1, …, D_L}` is feasible for (ℓp-ultrametric-LP), and its LP objective is `‖U − X‖_p^p`. This is
the relaxation property the proof of Theorem 1 (p.15) uses "together with Lemma 4". -/
theorem integer_point {n : ℕ} (X : Fin n → Fin n → ℝ) (hX : IsInstance X)
    (U : Fin n → Fin n → ℝ) (hU : IsUltrametric U)
    (hval : ∀ i j, i ≠ j → ∃ ℓ ∈ Finset.Icc 1 (numLayers X), U i j = layerValue X ℓ)
    (p : ℝ) (hp : 1 ≤ p) :
    IsFeasible X (integerPoint X U) ∧ lpCost X p (integerPoint X U) = lpDist p U X ^ p := by sorry

end UltrametricFit
