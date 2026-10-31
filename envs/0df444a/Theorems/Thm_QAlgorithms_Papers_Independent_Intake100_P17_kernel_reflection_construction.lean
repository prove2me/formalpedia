-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P17_kernel_reflection_construction
-- name    : QAlgorithms.Papers.Independent.Intake100.P17.kernel_reflection_construction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:25:14.542102+00:00
-- url     : https://prove2.me/theorems/dd14c4d7-fbcf-4560-b004-dca457933360
-- title:
--   Weighted RKHS action gives a reflection-positive subspace
-- statement:
--   Let \((G,\tau,S)\) be a symmetric group with a sharp-invariant subsemigroup, acting on a set \(X\), and let \(r\) be the involution of \(X\) implementing \(\tau\). Let \(K:X\times X\to\mathbb C\) be a positive definite kernel with reproducing kernel Hilbert space \(E\); write \(k_x\) for its kernel vector. Assume that the action extends unitarily to \(G\rtimes\{1,\tau\}\), acts on functions by \((\pi(g)f)(x)=J_g(x)f(g^{-1}x)\) with nonzero complex weights, and that \((\theta f)(x)=f(r x)\), so the reflection weight is one. Let \(D\subseteq X\) be \(S\)-invariant, and suppose \(K^\tau(x,y)=K(x,r y)\) is positive definite on \(D\).
--
--   Then
--   \[
--   \pi(g)k_x=\overline{J_{g^{-1}}(x)}\,k_{gx},\qquad
--   E_+=\overline{\operatorname{span}\{k_x:x\in D\}}
--   \]
--   is invariant under \(\pi(S)\), and \(\langle\theta v,v\rangle\ge0\) for every \(v\in E_+\), using the source's first-linear inner product.
--
--   This construction turns positivity of a reflected kernel into a reflection-positive Hilbert subspace. **Formalization Note** Continuous evaluation, the reproducing identity, injectivity and total kernel vectors describe the assumed RKHS; the unitary weighted action is assumed exactly as in the source.
-- source:
--   Reflection Positivity and Conformal Symmetry, arXiv:1206.2039v2, PDF p. 9, Example 1.7(a): kernel construction

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P17

noncomputable section

open scoped BigOperators Topology

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Intake100.P17

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

/-- Example 1.7(a), PDF p. 9: an assumed unitary weighted RKHS action and a positive
reflected kernel give the invariant theta-positive closed span. Equation (8) includes
complex conjugation over the weight, visible in the PDF. -/
theorem kernel_reflection_construction
    {G E : Type*} {X : Type} [Group G] [MulAction G X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (tau : G ≃* G) (htau : Function.Involutive tau)
    (S : Subsemigroup G) (hsharp : ∀ s ∈ S, (tau s)⁻¹ ∈ S)
    (r : X → X) (hr : Function.Involutive r)
    (hrcov : ∀ g x, r (g • r x) = tau g • x)
    (K : X → X → ℂ) (hK : PositiveKernel K)
    (R : ReflectionAction G tau E) (J : G → X → ℂˣ)
    (ev : E →L[ℂ] X → ℂ) (hev : Function.Injective ev) (k : X → E)
    (hrepro : ∀ v x, ev v x = inner ℂ (k x) v)
    (hkernel : ∀ x y, ev (k y) x = K x y)
    (htotal : (Submodule.span ℂ (Set.range k)).topologicalClosure = ⊤)
    (hweighted : ∀ g v x, ev (R.pi g v) x = (J g x : ℂ) * ev v (g⁻¹ • x))
    (hreflection : ∀ v x, ev (R.theta v) x = ev v (r x))
    (D : Set X) (hD : ∀ s ∈ S, ∀ x ∈ D, s • x ∈ D)
    (hKD : PositiveKernel (fun (x y : D) => K x (r y))) :
    (∀ g x, R.pi g (k x) = star (J g⁻¹ x : ℂ) • k (g • x)) ∧
    (let P := (Submodule.span ℂ (k '' D)).topologicalClosure
     (∀ s ∈ S, ∀ v ∈ P, R.pi s v ∈ P) ∧ ThetaPositive R.theta P) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P17

end
