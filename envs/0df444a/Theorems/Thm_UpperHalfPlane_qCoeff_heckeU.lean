-- Prove2me | Theorems.Thm_UpperHalfPlane_qCoeff_heckeU
-- name    : UpperHalfPlane.qCoeff_heckeU
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/5e125770-bc42-5e19-840f-ad504c602b22
-- title:
--   q-expansion coefficients of Uₚ f: aₙ(Uₚf)=aₙₚ(f)
-- statement:
--   Let $f:\mathbb H\to\mathbb C$ be a function on the upper half-plane subject to three hypotheses: its extension to $\mathbb C$ by `UpperHalfPlane.ofComplex` is periodic of period $1$; $f$ is holomorphic, in the sense of being differentiable as a map of complex manifolds modelled on $\mathbb C$; and $f$ is bounded at $i\infty$. Let $k\in\mathbb Z$, let $p$ be a natural number with $p\neq 0$, and let $n$ be a natural number. Here [`ModularFormClass.qCoeff f m`](def/FLTPrelim_Modularity.html#L19) denotes the $m$-th coefficient of the $q$-expansion of $f$ taken with respect to the period $1$, and [`ModularForm.heckeU k p f`](def/ModularForm_HeckeOperator.html#L93) is the sum $\sum_{j<p} f\mid[k]\,\gamma_j$ of weight-$k$ slash actions of the matrices $\gamma_j=\begin{pmatrix}1&j\\0&p\end{pmatrix}$ in $\mathrm{GL}_2(\mathbb R)$, for $j=0,\dots,p-1$; with the determinant normalisation of the slash action this is $\tau\mapsto p^{-1}\sum_{j<p} f((\tau+j)/p)$. The assertion is that the $n$-th $q$-expansion coefficient of [`ModularForm.heckeU k p f`](def/ModularForm_HeckeOperator.html#L93) equals [`ModularForm.coeffHeckeU p (qCoeff f) n`](def/ModularForm_HeckeOperator.html#L165), that is, the $(np)$-th $q$-expansion coefficient of $f$. No invariance of $f$ under any congruence subgroup is assumed, and the weight $k$ enters only through the slash action.
--
--   This is the classical computation of the effect of the Hecke operator $U_p$ on $q$-expansions, $a_n(U_pf)=a_{np}(f)$, stated here for an arbitrary $1$-periodic holomorphic function bounded at $i\infty$ rather than only for modular forms. It serves as the coefficient-level input for the arguments about $U_p$- and $T_p$-eigenforms used in the level-lowering part of the development, for instance in the analysis of eigenforms after change of level and in the comparison of $U_p$ with degeneracy maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_qCoeff_heckeU.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem UpperHalfPlane.qCoeff_heckeU {f : UpperHalfPlane → ℂ} (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) (k : ℤ) {p : ℕ} (hp : p ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (ModularForm.heckeU k p f) n = ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n := by sorry
