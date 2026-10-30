-- Prove2me | Theorems.Thm_WassersteinDRO_ConvexLossP1_eq_13_lip_modulus_eq_sup_dom_conjugate
-- name    : WassersteinDRO.ConvexLossP1.eq_13_lip_modulus_eq_sup_dom_conjugate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:53:52.110833+00:00
-- url     : https://prove2.me/theorems/1aa8b57c-2ecf-43d6-90ce-66b5eb9c2041
-- title:
--   Eq. (13): $\mathrm{Lip}(\ell) = \sup\{\|z\|_* : \ell^*(z) < \infty\}$
-- statement:
--   Let $(E, \|\cdot\|)$ be a finite-dimensional real normed space with dual norm $\|\cdot\|_*$, and let $\ell : E \to [-\infty, +\infty]$ be convex and upper semicontinuous, with $\ell(\xi_0) \in \mathbb R$ for some $\xi_0 \in E$. Then
--   $$\mathrm{Lip}(\ell) = \sup\{\|z\|_* : z \in E^*, \ \ell^*(z) < \infty\},$$
--   an identity in $[0, \infty]$.
--
--   In words: the Lipschitz modulus of a convex loss is the radius of the smallest dual-norm ball around $0$ that contains the domain of its conjugate. Together with Theorem 10 it shows that evaluating the type-1 worst-case risk of a convex loss amounts to maximizing a norm over the domain of the conjugate, which the paper uses to show that the problem is hard in general.
--
--   Upper semicontinuity cannot be dropped: on $\mathbb R$, the function equal to $-\infty$ on $(-\infty, 0)$, to $0$ at $0$ and to $+\infty$ on $(0, \infty)$ is convex with a finite value, its conjugate is identically $+\infty$, so the right side is $0$ while $\mathrm{Lip}(\ell) = \infty$.
--
--   Differences from the source:
--   - generalization: ℓ the loss of Theorem 10 (convex, measurable, upper semicontinuous, P̂N-integrable by Assumption 1) → ℓ convex, upper semicontinuous, with at least one finite value; reason: a P̂N-integrable loss is finite at the samples (N ≥ 1), so the paper's losses satisfy the hypotheses.
--   - encoding: convexity of an extended real-valued ℓ → convexity of the epigraph (`IsConvexExt`); reason: the standard definition for extended real-valued functions.
--   - encoding: z ∈ R^m with z^⊤ξ and ‖z‖∗ = sup_{‖ξ‖≤1} z^⊤ξ → z a continuous linear functional on E with its operator norm; reason: the same objects on a finite-dimensional space.
--   - encoding: R^m with an arbitrary norm → a finite-dimensional real normed space E; reason: same instances up to linear isometry.
--   - encoding: |ϕ(ξ) − ϕ(ξ′)| undefined when both values are the same infinity → valued ∞ in `lipModulus`; reason: changes no value when ℓ has a finite value, which is a hypothesis.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, Remark 3, eq. (13), p. 14

import Mathlib
import Definitions.Def_WassersteinDRO_ConvexLossP1_IsConvexExt
import Definitions.Def_WassersteinDRO_ConvexLossP1_lipModulus
import Definitions.Def_WassersteinDRO_ConvexLossP1_conjugate

namespace WassersteinDRO.ConvexLossP1

/-- **Eq. (13): the Lipschitz modulus is the radius of the domain of the conjugate.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, Remark 3 (Computing the Lipschitz modulus), eq. (13), p. 14: "One can show that
Lip(ℓ) = sup{‖z‖∗ : ℓ∗(z) < ∞}, (13) that is, the Lipschitz modulus of ℓ(ξ) coincides with the
radius of the smallest dual norm ball around 0 that encloses the domain of the conjugate loss
function ℓ∗(z) [61, § 6.2]." The loss is that of Theorem 10 (convex), under Assumption 1, p. 9
(upper semicontinuous, integrable with respect to `P̂_N`).

For every convex, upper semicontinuous `ℓ : E → [−∞, ∞]` that takes at least one finite value:
`Lip(ℓ) = sup {‖z‖∗ : z ∈ E*, ℓ*(z) < ∞}`, an identity in `[0, ∞]`.

**Formalization Note.** Convexity is epigraph convexity (`IsConvexExt`). The dual norm `‖z‖∗` is
the operator norm of `z : StrongDual ℝ E`. The paper's context is the loss of Theorem 10, which is
`P̂_N`-integrable and so finite at the samples; only one finite value is required here.
Upper semicontinuity cannot be dropped: on `ℝ`, `ℓ = −∞` on `(−∞, 0)`, `ℓ(0) = 0`, `ℓ = +∞` on
`(0, ∞)` is convex with a finite value, `ℓ* ≡ +∞`, so the right side is `0` while `Lip(ℓ) = ∞`. -/
theorem eq_13_lip_modulus_eq_sup_dom_conjugate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (ℓ : E → EReal) (hconv : IsConvexExt ℓ)
    (husc : UpperSemicontinuous ℓ) (hfin : ∃ ξ0 : E, ℓ ξ0 ≠ ⊤ ∧ ℓ ξ0 ≠ ⊥) :
    lipModulus ℓ = ⨆ (z : StrongDual ℝ E) (_ : conjugate ℓ z < ⊤), (‖z‖₊ : ENNReal) := by sorry

end WassersteinDRO.ConvexLossP1
