-- Prove2me | Theorems.Thm_SWSSNet_Diffusion_proposition_2
-- name    : SWSSNet.Diffusion.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:58.169491+00:00
-- url     : https://prove2.me/theorems/66122cc9-6846-4848-8661-b627e1153517
-- title:
--   Proposition 2 — for every edge (î, ĵ), b(x,u) = h − B₁(x − ⟨e,x⟩⁺u^c) + ⟨e,x⟩⁻B₂u^s with B₁ lower triangular (î last), (B₁)_îî = µ_îĵ, last column of B₂ zero
-- statement:
--   Let $(\hat\imath,\hat\jmath)$ be an edge of the tree, and let $B_1,B_2$ be the matrices of (38) for the pool $\hat\jmath$. Then:
--
--   1. For every constant vector $h$, every state $x\in\mathbb R^I$ and every control value $u=(u^c,u^s)\in\Delta_I\times\Delta_J$, the drift (42) has the representation
--   $$
--   b(x,u)=h-B_1\big(x-\langle e,x\rangle^+u^c\big)+\langle e,x\rangle^-B_2u^s. \qquad (43)
--   $$
--   2. There is an ordering of the classes in which $\hat\imath$ comes last and $B_1$ is lower triangular.
--   3. Every diagonal entry of $B_1$ is positive, and $(B_1)_{\hat\imath\hat\imath}=\mu_{\hat\imath\hat\jmath}$.
--   4. The column $\hat\jmath$ of $B_2$, the last column in the basis $(\alpha,(\beta)_{-\hat\jmath})$, is identically zero.
--
--   The representation turns the network drift into a piecewise-linear vector field with a triangular linear part. Theorems 3–5 and the stability analysis of Theorem 7 work with this form.
--
--   **Formalization Note** The paper states (43) with $h$ of (12); the identity does not depend on $h$, and is stated for every constant vector. "Lower diagonal with respect to the ordered basis with $\alpha_{\hat\imath}$ last" is rendered as a permutation `rk` of the classes with $\hat\imath$ maximal and $(B_1)_{kl}=0$ whenever $k$ precedes $l$.
-- source:
--   Hmedi, Arapostathis & Pang, On System-Wide Safety Staffing of Large-Scale Parallel Server Networks, arXiv:2009.01942v3, p. 18, Proposition 2 and (43); B₁, B₂ from (38), p. 17

import Mathlib
import Definitions.Def_SWSSNet_Diffusion_Network

open Matrix MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace SWSSNet.Diffusion

/-- Proposition 2, p. 18: for every edge `(î, ĵ)` the drift (42) equals
`h − B₁(x − ⟨e,x⟩⁺u^c) + ⟨e,x⟩⁻B₂u^s` (43) on control values; `B₁` is lower triangular in an
ordering of the classes in which `î` comes last, with positive diagonal and `(B₁)_{îî} = µ_{îĵ}`;
and the column `ĵ` of `B₂` (the last in the basis `(α, (β)_{−ĵ})`) vanishes. -/
theorem proposition_2 {I J : ℕ} (N : TreeNetwork I J) (î : Fin I) (ĵ : Fin J) (hedge : N.adj î ĵ) :
    (∀ (hv : Fin I → ℝ) (u : (Fin I → ℝ) × (Fin J → ℝ)) (x : EthierKurtz.SDEState I),
      IsControlValue u →
      driftH N hv u x = WithLp.toLp 2 (hv - B1 N ĵ *ᵥ (fun k => x k - max (∑ l, x l) 0 * u.1 k)
        + max (-(∑ k, x k)) 0 • (B2 N ĵ *ᵥ u.2))) ∧
    (∃ rk : Fin I ≃ Fin I, (∀ k, rk k ≤ rk î) ∧ ∀ k l, rk k < rk l → B1 N ĵ k l = 0) ∧
    (∀ i, 0 < B1 N ĵ i i) ∧
    B1 N ĵ î î = N.mu î ĵ ∧
    ∀ i, B2 N ĵ i ĵ = 0 := by sorry

end SWSSNet.Diffusion
