-- Prove2me | Theorems.Thm_WeierstrassCurve_Generic_exists_algEquiv_inLine_of_eval_prePsi_eq_zero_of_ne_zero
-- name    : WeierstrassCurve.Generic.exists_algEquiv_inLine_of_eval_prePsi_eq_zero_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/8bebd2f3-faee-55d1-92a4-153ed12b3fcc
-- title:
--   Galois transitivity on cyclic p-subgroups of the generic curve
-- statement:
--   Let $K$ be a field, let $p$ be a prime (as a `Fact` instance) with $p \neq 2$ and $(p : K) \neq 0$. Write [`WeierstrassCurve.Generic.FunctionField K`](def/WeierstrassCurve_Generic.html#L91) for the fraction field of $K[X_0,\dots,X_4]$ (polynomials in five variables indexed by `Fin 5`), [`WeierstrassCurve.Generic.Closure K`](def/WeierstrassCurve_Generic.html#L93) for an algebraic closure $\Omega$ of that field, and [`WeierstrassCurve.Generic.curve K`](def/WeierstrassCurve_Generic.html#L95) for the generic Weierstrass curve over $\Omega$, i.e. the curve with coefficients $a_1 = X_0$, $a_2 = X_1$, $a_3 = X_2$, $a_4 = X_3$, $a_6 = X_4$ pushed forward along the structure map. Let $x, x' \in \Omega$ both be roots of the polynomial `preΨ p` of this curve. The assertion is that there is an algebra automorphism $\sigma$ of $\Omega$ over `FunctionField K` such that [`ModularCurve.InLine (curve K) p (σ x) x'`](def/ModularCurve_KatzLevelP.html#L21) holds, that is, such that for some natural number $a$ with $1 \le a$ and $a \le (p-1)/2$ one has $x' \cdot (\Psi^2_a)(\sigma x) = \Phi_a(\sigma x)$, where $\Psi^2_a$ and $\Phi_a$ are the polynomials `ΨSq a` and `Φ a` attached to the curve.
--
--   Since $x'\,\Psi_a^2 = \Phi_a$ expresses that the abscissa $x'$ is the abscissa of $a$ times a point with abscissa $\sigma x$, the statement says that the Galois group of the generic Weierstrass equation permutes the cyclic subgroups of order $p$ of the generic elliptic curve transitively; this is the irreducibility of the modular curve $X_0(p)$ over $K$ (Weber–Fricke in characteristic $0$, Igusa in characteristic $\ell \neq p$), phrased in terms of division polynomials. It is used in the proofs that a Katz level-$p$ form depending only on lines, respectively only on the second line, and vanishing at the cusp vanishes identically over a field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Generic_exists_algEquiv_inLine_of_eval_prePsi_eq_zero_of_ne_zero.lean

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_WeierstrassCurve_Generic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem WeierstrassCurve.Generic.exists_algEquiv_inLine_of_eval_prePsi_eq_zero_of_ne_zero
    {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : (p : K) ≠ 0)
    {x x' : WeierstrassCurve.Generic.Closure K}
    (hx : ((WeierstrassCurve.Generic.curve K).preΨ p).eval x = 0)
    (hx' : ((WeierstrassCurve.Generic.curve K).preΨ p).eval x' = 0) :
    ∃ σ : WeierstrassCurve.Generic.Closure K ≃ₐ[WeierstrassCurve.Generic.FunctionField K]
        WeierstrassCurve.Generic.Closure K,
      ModularCurve.InLine (WeierstrassCurve.Generic.curve K) p (σ x) x' := by sorry
