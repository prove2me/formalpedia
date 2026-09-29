-- Prove2me | Theorems.Thm_WeierstrassCurve_IsCyclicGenKernel_exists_moduleFinite_represents
-- name    : WeierstrassCurve.IsCyclicGenKernel.exists_moduleFinite_represents
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/1d307763-8cb2-56fd-b952-53e37e04af5f
-- title:
--   Representability of cyclic generator-kernel polynomials by a finite B-algebra
-- statement:
--   Let $B$ be a commutative ring in a universe $u$, let $W$ be a Weierstrass curve over $B$, let $p$ be a prime and $k$ a natural number with $3 \le p^{k}$, and assume that $p \cdot \Delta_W$ is a unit of $B$. Then there exist a commutative ring $C$ in the same universe, a $B$-algebra structure on $C$ making $C$ module-finite over $B$, and a polynomial $h_{\mathrm u} \in C[X]$ satisfying `IsCyclicGenKernel` for the base-changed curve $W_C$ at $p, k$, that is: writing $d = \varphi(p^{k})/2$ (Euler totient, natural division), $\deg h_{\mathrm u} \le d$, the coefficient of $X^{d}$ in $h_{\mathrm u}$ is $1$, the product $h_{\mathrm u} \cdot \mathrm{pre}\Psi_{p^{k-1}}(W_C)$ divides $\mathrm{pre}\Psi_{p^{k}}(W_C)$ (here $k-1$ is truncated subtraction), and for every $a$ with $2 \le a \le (p^{k}-1)/2$ and $p \nmid a$ the polynomial $h_{\mathrm u}$ divides $\sum_{i=0}^{d} (h_{\mathrm u})_i \, \Phi_a^{\,i} \, \Psi_a^{2\,(d-i)}$; and such that the pair $(C, h_{\mathrm u})$ is universal: for every commutative ring $T$ in universe $u$, every ring homomorphism $\varphi : B \to T$ and every $h \in T[X]$, the curve $W$ pushed forward along $\varphi$ satisfies the same four conditions with $h$ if and only if there is a unique ring homomorphism $\psi : C \to T$ with $\psi \circ (\text{structure map } B \to C) = \varphi$ and $h = \psi_*h_{\mathrm u}$.
--
--   This is the representability statement for the functor of $\Gamma_0(p^{k})$-type generator-kernel polynomials on a fixed Weierstrass curve with $p\Delta$ invertible, in the style of the moduli-theoretic treatment of level structures on elliptic curves: the functor sending a $B$-algebra $T$ to the set of $h \in T[X]$ satisfying `IsCyclicGenKernel` at $(p,k)$ is represented by a module-finite $B$-algebra. It is used by [`ModularCurve.IsGamma0PowAt.exists_moduleFinite_represents_tuple`](thm.html#ModularCurve.IsGamma0PowAt.exists_moduleFinite_represents_tuple), where the corresponding statement for tuples of such data is assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_IsCyclicGenKernel_exists_moduleFinite_represents.lean

import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem WeierstrassCurve.IsCyclicGenKernel.exists_moduleFinite_represents
    {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p k : ℕ) [Fact p.Prime] (hpk : 3 ≤ p ^ k)
    (hu : IsUnit ((p : B) * W.Δ)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C) (_ : Module.Finite B C) (hᵤ : Polynomial C)
      (_ : (W.map (algebraMap B C)).IsCyclicGenKernel p k hᵤ),
      ∀ (T : Type u) [CommRing T] (φ : B →+* T) (h : Polynomial T),
        (W.map φ).IsCyclicGenKernel p k h ↔
          ∃! ψ : C →+* T, ψ.comp (algebraMap B C) = φ ∧ hᵤ.map ψ = h := by sorry
