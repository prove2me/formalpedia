-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj
-- name    : WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/8486e300-4d51-5173-820b-eb8a99a80e39
-- title:
--   Cyclic kernel and its order transport along function-field isomorphisms
-- statement:
--   Let $E,E',D,D'$ be affine Weierstrass curves over $\mathbb{C}$, each elliptic and each carrying the three project structures: a `GenusOnePlaceGate` (a bijection between the group of points of the curve and the places of its function field over $\mathbb{C}$, all of which have degree $1$), its `IsCentred` refinement (at the place attached to a point $(x,y)$, the images in the function field of the coordinate-ring classes of $X-x$ and of $Y-y$ lie in the nonunits of the valuation subring), and `AbelTheorem` (a divisor of degree $0$ is principal exactly when its divisor sum vanishes). Let $\iota : \mathbb{C}(E') \to \mathbb{C}(E)$ be a $\mathbb{C}$-algebra map whose underlying ring homomorphism is integral, such that $\mathbb{C}(E)$ is a finite module over $\mathbb{C}(E')$ along $\iota$ and the pushforward norm formula holds along $\iota$: for every nonzero $f \in \mathbb{C}(E)$ and every divisor $D$ with $D(w) = \operatorname{ord}_w f$ for all places $w$ of $\mathbb{C}(E)$, the pushforward of $D$ satisfies $(\iota_* D)(v) = \operatorname{ord}_v(N(f))$ at every place $v$ of $\mathbb{C}(E')$. Let $e_E : \mathbb{C}(D) \simeq \mathbb{C}(E)$ and $e_{E'} : \mathbb{C}(D') \simeq \mathbb{C}(E')$ be $\mathbb{C}$-algebra isomorphisms, and let $\iota'' : \mathbb{C}(D') \to \mathbb{C}(D)$ be a $\mathbb{C}$-algebra map, again integral, finite and satisfying the norm formula, which makes the square commute: $e_E(\iota''(x)) = \iota(e_{E'}(x))$ for all $x$. Here `pointMapOfPushforward` denotes the homomorphism of point groups obtained by transporting the pushforward map on degree-zero divisor classes through the isomorphisms between points and $\mathrm{Pic}^0$ supplied by the gates, so that $\iota$ gives a map $E(\mathbb{C}) \to E'(\mathbb{C})$ and $\iota''$ a map $D(\mathbb{C}) \to D'(\mathbb{C})$. Assuming the kernel of the map attached to $\iota$ is cyclic, the conclusion is that the kernel of the map attached to $\iota''$ is cyclic as well, and that the two kernels have the same cardinality.
--
--   This is the transport statement saying that the cyclicity of the kernel of a pushforward point map, and the order of that kernel, depend only on the function-field data up to $\mathbb{C}$-algebra isomorphism of the source and target function fields. It feeds the step [`WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward`](thm.html#WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward), where a cyclic kernel of prescribed order between two complex elliptic curves is converted into the vanishing of the corresponding modular polynomial at the pair of $j$-invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

theorem WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj
    (E E' D D' : WeierstrassCurve.Affine ℂ) [E.IsElliptic] [E'.IsElliptic] [D.IsElliptic] [D'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    [GenusOnePlaceGate D] [GenusOnePlaceGate.IsCentred D] [AbelTheorem D]
    [GenusOnePlaceGate D'] [GenusOnePlaceGate.IsCentred D'] [AbelTheorem D']
    (ι : E'.FunctionField →ₐ[ℂ] E.FunctionField) (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι)
    (hN : NormFormulaAlong ℂ ι hfin)
    (eE : D.FunctionField ≃ₐ[ℂ] E.FunctionField) (eE' : D'.FunctionField ≃ₐ[ℂ] E'.FunctionField)
    (ι'' : D'.FunctionField →ₐ[ℂ] D.FunctionField) (hconj : ∀ x, eE (ι'' x) = ι (eE' x))
    (hι'' : ι''.toRingHom.IsIntegral) (hfin'' : FiniteAlong ℂ ι'') (hN'' : NormFormulaAlong ℂ ι'' hfin'')
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker) :
    IsAddCyclic (pointMapOfPushforward ι'' hι'' hfin'' hN'').ker ∧
      Nat.card (pointMapOfPushforward ι'' hι'' hfin'' hN'').ker = Nat.card (pointMapOfPushforward ι hι hfin hN).ker := by sorry
