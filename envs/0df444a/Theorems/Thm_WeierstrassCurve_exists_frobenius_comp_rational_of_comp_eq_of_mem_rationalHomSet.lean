-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_frobenius_comp_rational_of_comp_eq_of_mem_rationalHomSet
-- name    : WeierstrassCurve.exists_frobenius_comp_rational_of_comp_eq_of_mem_rationalHomSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/dcb5089c-700d-58f9-88f3-bfb03c33eb3a
-- title:
--   Rational factorisation up to Frobenius twist
-- statement:
--   Let $F$ be a field, $k$ an algebraically closed field with an $F$-algebra structure, and let $W_1,W_2,W_3$ be Weierstrass curves over $F$, each assumed elliptic. Write $E_i(k)$ for the group of points of the affine curve obtained from $W_i$ by base change to $k$, and for $p \in F[X][Y]$ let `evalEvalBC` $k\,p\,x\,y$ denote the value at $(x,y) \in k^2$ of the image of $p$ under the coefficientwise map $F \to k$. Let $\rho \colon E_1(k) \to E_2(k)$ and $\psi \colon E_1(k) \to E_3(k)$ be additive maps, each assumed to lie in `rationalHomSet`, that is: each is either the zero map or is $F$-rationally represented, meaning there are $n_X,d_X,n_Y,d_Y \in F[X][Y]$ and a finite $B \subseteq k$ such that for every affine point $(x,y)$ of the base-changed curve with $x \notin B$ the values of $d_X$ and $d_Y$ at $(x,y)$ are nonzero and the map sends that point to the affine point with coordinates $n_X(x,y)/d_X(x,y)$, $n_Y(x,y)/d_Y(x,y)$. Assume $\psi \neq 0$, and let $\mu \colon E_2(k) \to E_3(k)$ be an additive map with $\mu \circ \rho = \psi$. Then there exist $t \in \mathbb{N}$, polynomials $n_X,d_X,n_Y,d_Y \in F[X][Y]$ and a finite set $B \subseteq k$ such that for every affine point $(x,y)$ of the base change of $W_2$ with $x \notin B$: the values of $d_X$ and $d_Y$ at $(x,y)$ are nonzero, and $\mu$ sends that point to an affine point $(x',y')$ of the base change of $W_3$ satisfying
--   $$x'^{\,q} = \frac{n_X(x,y)}{d_X(x,y)}, \qquad y'^{\,q} = \frac{n_Y(x,y)}{d_Y(x,y)}, \qquad q = (\operatorname{ringExpChar} F)^t,$$
--   with $\operatorname{ringExpChar} F$ the characteristic exponent of $F$.
--
--   This is the statement that a set-theoretic factorisation $\psi = \mu \circ \rho$ of homomorphisms of elliptic curves is itself algebraic and defined over $F$, up to composition with a $q$-power Frobenius absorbing the inseparability of $\rho$; note that the conclusion is weaker in shape than membership of $\mu$ in `rationalHomSet`, the rational formulae computing only the $q$-th powers of the coordinates of $\mu$ of a point (in characteristic $0$ one has $q = 1$ and the two coincide). It is used in the construction of dual pairs of rational homomorphisms and in producing a rational homomorphism through which a given one factors when the kernel condition holds; the proof cites the surjectivity of a nonzero element of `rationalHomSet`, the nonvanishing of $\Psi_2^2$ for an elliptic Weierstrass curve, and a one-variable result on factoring rational maps through Frobenius iterates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_frobenius_comp_rational_of_comp_eq_of_mem_rationalHomSet.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_frobenius_comp_rational_of_comp_eq_of_mem_rationalHomSet {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W₁ W₂ W₃ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic] {ρ : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point} {ψ : (W₁.baseChange k).toAffine.Point →+ (W₃.baseChange k).toAffine.Point} (hρ : ρ ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) (hψ : ψ ∈ WeierstrassCurve.rationalHomSet k W₁ W₃) (hψ0 : ψ ≠ 0) {μ : (W₂.baseChange k).toAffine.Point →+ (W₃.baseChange k).toAffine.Point} (hμ : μ.comp ρ = ψ) : ∃ (t : ℕ) (nX dX nY dY : Polynomial (Polynomial F)) (B : Set k), B.Finite ∧ ∀ (x y : k) (h : (W₂.baseChange k).toAffine.Nonsingular x y), x ∉ B → WeierstrassCurve.evalEvalBC k dX x y ≠ 0 ∧ WeierstrassCurve.evalEvalBC k dY x y ≠ 0 ∧ ∃ (x' y' : k) (h' : (W₃.baseChange k).toAffine.Nonsingular x' y'), μ (WeierstrassCurve.Affine.Point.some x y h) = WeierstrassCurve.Affine.Point.some x' y' h' ∧ x' ^ ringExpChar F ^ t = WeierstrassCurve.evalEvalBC k nX x y / WeierstrassCurve.evalEvalBC k dX x y ∧ y' ^ ringExpChar F ^ t = WeierstrassCurve.evalEvalBC k nY x y / WeierstrassCurve.evalEvalBC k dY x y := by sorry
