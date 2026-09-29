-- Prove2me | Theorems.Thm_WeierstrassCurve_isModularModelOfExactConductorLevel_of_level_conductorLevel
-- name    : WeierstrassCurve.isModularModelOfExactConductorLevel_of_level_conductorLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/d7e13979-b6a9-5758-9888-2ca4029af339
-- title:
--   Level rad|Δ| modularity gives exact-conductor-level modularity
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta(W) \neq 0$, and assume that $W$ `IsModularModelOfLevel` at its conductor level $N_0 = \operatorname{rad}|\Delta(W)|$, the radical of the natural absolute value of the discriminant; that is, there is a weight-$2$ cusp form $f$ for $\Gamma_0(N_0)$ which is a normalised eigenform in the sense that its $q$-expansion coefficients satisfy $a_1(f) = 1$, $a_{mn}(f) = a_m(f)a_n(f)$ for coprime $m, n$, $a_{p^{r+2}}(f) = a_p(f)a_{p^{r+1}}(f) - p\,a_{p^r}(f)$ for primes $p \nmid N_0$ and $a_{p^{r+2}}(f) = a_p(f)a_{p^{r+1}}(f)$ for primes $p \mid N_0$, and such that for every prime $p$ with $p \nmid \Delta(W)$ and $p \nmid N_0$ one has $a_p(f) = \operatorname{tr}(\mathrm{Frob}_p)$ on the reduction of $W$ modulo $p$. The conclusion is `IsModularModelOfExactConductorLevel`: there exists a natural number $N$ which is positive, squarefree, satisfies $q \mid N \iff q \mid \Delta(W)$ for every prime $q$, and for which $W$ is a modular model of level $N$ in the above sense.
--
--   This is the repackaging step that converts a modularity statement at the specific level $\operatorname{rad}|\Delta|$ into the level-agnostic "exact conductor level" form — positive squarefree level whose prime support is exactly the set of primes of bad reduction — in which modularity hypotheses are consumed downstream. It is used by the modularity-lifting statements at the conductor level for the primes $3$ and $5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isModularModelOfExactConductorLevel_of_level_conductorLevel.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ConductorLevel
import Definitions.Def_WeierstrassCurve_ModularityLiftingConductor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.isModularModelOfExactConductorLevel_of_level_conductorLevel
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (h : W.IsModularModelOfLevel W.conductorLevel) :
    W.IsModularModelOfExactConductorLevel := by sorry
