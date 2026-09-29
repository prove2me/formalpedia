-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_heq_vcInvFun_iff_exists_dualPair
-- name    : WeierstrassCurve.exists_variableChange_heq_vcInvFun_iff_exists_dualPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/9678cda1-e473-5943-917a-db147e1c7380
-- title:
--   Universality of the ℓ-isogeny quotient with level structure
-- statement:
--   Let $\kappa$ be an algebraically closed field and let $E$, $A$, $E'$ be Weierstrass curves over $\kappa$ that are elliptic (invertible discriminant). Let $\ell$ be a prime that is nonzero in $\kappa$, and let $Q$ be a point of the affine model of $E$ with $\mathrm{ord}(Q)=\ell$. Call an additive map between groups of affine points of (base-changed) Weierstrass curves *rational*, i.e. a member of [`WeierstrassCurve.rationalHomSet`](def/WeierstrassCurve_RationalEnd.html#L28), if it is the zero map or else there are four polynomials $n_X,d_X,n_Y,d_Y\in\kappa[X][Y]$ and a finite set $B\subseteq\kappa$ such that for every nonsingular point $(x,y)$ of the source with $x\notin B$ the denominators $d_X,d_Y$ do not vanish at $(x,y)$ and the map sends $(x,y)$ to $(n_X/d_X,\,n_Y/d_Y)$ evaluated there. Assume $\varphi\colon E\to A$ is a rational additive map with $\ker\varphi=\langle Q\rangle$ which is universal among such: for every elliptic Weierstrass curve $V$ over $\kappa$ and every rational additive $\alpha\colon E\to V$ with $\alpha(Q)=0$ there is a rational $\beta\colon A\to V$ with $\alpha=\beta\circ\varphi$. Let $C$ and $C'$ be arbitrary sets of affine points of $E$ and of $E'$. Then the following are equivalent: (1) there is a variable change $\gamma=(u,r,s,t)$ over $\kappa$ with $\gamma\cdot A=E'$ such that the induced map $(x,y)\mapsto (u^{-2}(x-r),\,u^{-3}(y-t-s(x-r)))$, sending $0$ to $0$, carries $\varphi(T)$ to a point of $C'$ (as a heterogeneous equality, the types agreeing by $\gamma\cdot A=E'$) for every $T\in C$; (2) there are rational additive maps $\psi\colon E\to E'$ and $\psi'\colon E'\to E$ with $\ker\psi=\langle Q\rangle$, $\psi'\circ\psi=[\ell]$, $\psi\circ\psi'=[\ell]$, and $\psi(T)\in C'$ for all $T\in C$.
--
--   This is the statement that the universal quotient of $E$ by $\langle Q\rangle$ — realised, for instance, by Vélu's isogeny onto Vélu's model — is the target of every dual pair of $\ell$-isogenies from $E$ with kernel $\langle Q\rangle$, uniquely up to an admissible change of Weierstrass coordinates, with a prescribed set of points carried along. It is used in the analysis of the degeneracy and Hecke correspondences on modular curves, where an isomorphism of Weierstrass models together with its map on points is converted into a count of level-compatible $\ell$-isogenies.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_heq_vcInvFun_iff_exists_dualPair.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.exists_variableChange_heq_vcInvFun_iff_exists_dualPair
    {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (E A E' : WeierstrassCurve κ) [E.IsElliptic] [A.IsElliptic] [E'.IsElliptic]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ0 : (ℓ : κ) ≠ 0) (Q : E.toAffine.Point) (hQ : addOrderOf Q = ℓ)
    (φ : (E.baseChange κ).toAffine.Point →+ (A.baseChange κ).toAffine.Point)
    (hφ : φ ∈ WeierstrassCurve.rationalHomSet κ E A) (hker : φ.ker = AddSubgroup.zmultiples Q)
    (huniv : ∀ (V : WeierstrassCurve κ) [V.IsElliptic]
      (α : (E.baseChange κ).toAffine.Point →+ (V.baseChange κ).toAffine.Point),
        α ∈ WeierstrassCurve.rationalHomSet κ E V → α Q = 0 →
          ∃ β ∈ WeierstrassCurve.rationalHomSet κ A V, α = β.comp φ)
    (C : Set E.toAffine.Point) (C' : Set E'.toAffine.Point) :
    (∃ γ : WeierstrassCurve.VariableChange κ, γ • A = E' ∧
        ∀ T ∈ C, ∃ T' ∈ C', HEq (WeierstrassCurve.Affine.Point.vcInvFun γ A.toAffine (φ T)) T') ↔
      ∃ ψ ∈ WeierstrassCurve.rationalHomSet κ E E', ∃ ψ' ∈ WeierstrassCurve.rationalHomSet κ E' E,
        ψ.ker = AddSubgroup.zmultiples Q ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧
          ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧ ∀ T ∈ C, ψ T ∈ C' := by sorry
