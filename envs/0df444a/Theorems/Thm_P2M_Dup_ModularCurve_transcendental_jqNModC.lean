-- Prove2me | Theorems.Thm_P2M_Dup_ModularCurve_transcendental_jqNModC
-- name    : P2M.Dup.ModularCurve.transcendental_jqNModC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/c8fdab15-475e-5442-820a-8d73094da29d
-- title:
--   Transcendence of j(q^N) over the constants
-- statement:
--   Let $K$ be a field and let $N$ be a natural number that is nonzero. Consider the field $\mathrm{LaurentSeries}\,K$ of formal Laurent series over $K$ (Hahn series over $K$ with value group $\mathbb{Z}$), viewed as a $K$-algebra. Inside it, [`ModularCurve.jqModC K`](def/ModularCurve_JqCoeff.html#L15) is the product of the monomial $q^{-1}$ (the Hahn series `single (-1) 1`) with the image in $\mathrm{LaurentSeries}\,K$ of the integral power series `jNum`, its coefficients transported along the unique ring homomorphism $\mathbb{Z}\to K$; thus `jqModC K` is the $q$-expansion of the modular invariant $j$ read in $K$, with leading term $q^{-1}$. The ring homomorphism [`ModularCurve.qExpand K N`](def/ModularCurve_X0.html#L25) re-indexes exponents by multiplication by $N$, i.e. it performs the substitution $q\mapsto q^{N}$, and [`ModularCurve.jqNModC K N`](def/ModularCurve_JqCoeff.html#L18) is its value on `jqModC K`. The assertion is that this element is transcendental over $K$: no nonzero polynomial $P\in K[X]$ evaluates to $0$ at [`ModularCurve.jqNModC K N`](def/ModularCurve_JqCoeff.html#L18) under the $K$-algebra evaluation map.
--
--   This is the elementary transcendence statement that a Laurent series with a pole at $q=0$ satisfies no polynomial relation over the constant field, applied to the $q$-expansion of $j$ in the variable $q^{N}$. It is used in the treatment of modular curves and their function fields, notably in the full-level and $\Gamma_0$ statements identifying the image of the classifying maps through the condition that the $j$-invariant equals `jqNModC`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_transcendental_jqNModC.lean

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem P2M.Dup.ModularCurve.transcendental_jqNModC (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    Transcendental K (ModularCurve.jqNModC K N) := by sorry
