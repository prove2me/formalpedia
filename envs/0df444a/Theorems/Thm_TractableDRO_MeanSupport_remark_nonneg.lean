-- Prove2me | Theorems.Thm_TractableDRO_MeanSupport_remark_nonneg
-- name    : TractableDRO.MeanSupport.remark_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:33.582778+00:00
-- url     : https://prove2.me/theorems/517c23ac-9014-4aee-86f4-2ff65ca9bc15
-- title:
--   Remark after Theorem 1, p. 910 — if r⁰ + r′ζ ⩾ 0 on 𝒱, the worst case is r⁰ + sup over 𝒱̂ of r′ζ̂, attained in (21) at s = r
-- statement:
--   This is the first case of the Remark after Theorem 1 of Goh and Sim (2010).
--
--   Let $\mathcal V, \widehat{\mathcal V} \subseteq \mathbb R^n$ with $\widehat{\mathcal V}$ nonempty and $\widehat{\mathcal V} \subseteq \mathcal V$, and let $\mathbb F_1$ be the family of distributions with integrable coordinates, mean in $\widehat{\mathcal V}$ and support in $\mathcal V$. Let $r^0 \in \mathbb R$, $r \in \mathbb R^n$ satisfy $r^0 + r'\zeta \ge 0$ for all $\zeta \in \mathcal V$. Then
--   $$\sup_{\mathbb P \in \mathbb F_1} \mathbb E_{\mathbb P}\big((r^0 + r'\tilde\zeta)^+\big) = r^0 + \sup_{\hat\zeta \in \widehat{\mathcal V}} r'\hat\zeta,$$
--   and the infimum defining $\pi^1(r^0, r)$ in (21) is attained at $s = r$: writing $\Phi(s)$ for the objective of (21),
--   $$\Phi(r) = \pi^1(r^0, r).$$
--
--   When the affine function is nonnegative on the support, the positive part is inactive and the worst-case expectation reduces to a worst case over the mean set alone.
--
--   **Formalization Note** The page states the implication with no condition on the sets. As printed it fails when $\widehat{\mathcal V} \not\subseteq \mathcal V$ (for $\mathcal V = [0,1]$, $\widehat{\mathcal V} = [0,2]$, $r^0 = 0$, $r = 1$ the left side is $1$ and the right side is $2$), and when $\mathbb F_1 = \emptyset$. The paper's construction of $\mathcal V$ and $\widehat{\mathcal V}$ (§4.5) gives $\widehat{\mathcal V} \subseteq \mathcal V$; this and $\widehat{\mathcal V} \ne \emptyset$ are hypotheses here. Values are in `EReal`; $\Phi$ is `pi1Obj`.
-- source:
--   Goh & Sim, Distributionally Robust Optimization and Its Tractable Approximations, Oper. Res. 58(4), 2010, p. 910, Remark after Theorem 1 (first implication)

import Mathlib
import Definitions.Def_TractableDRO_MeanSupport_Model

open MeasureTheory

namespace TractableDRO.MeanSupport

theorem remark_nonneg {n : ℕ} (V Vhat : Set (Fin n → ℝ)) (hsub : Vhat ⊆ V)
    (hne : Vhat.Nonempty) (r0 : ℝ) (r : Fin n → ℝ) (hnn : ∀ ζ ∈ V, 0 ≤ r0 + r ⬝ᵥ ζ) :
    worstCase (family1 V Vhat) r0 r = (r0 : EReal) + ⨆ ζh ∈ Vhat, ((r ⬝ᵥ ζh : ℝ) : EReal) ∧
      pi1Obj V Vhat r0 r r = pi1 V Vhat r0 r := by sorry

end TractableDRO.MeanSupport
