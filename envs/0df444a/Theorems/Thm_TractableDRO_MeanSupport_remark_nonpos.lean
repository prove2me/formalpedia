-- Prove2me | Theorems.Thm_TractableDRO_MeanSupport_remark_nonpos
-- name    : TractableDRO.MeanSupport.remark_nonpos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:35.085642+00:00
-- url     : https://prove2.me/theorems/fffa59c7-32c9-4549-a9eb-c47ae54ae6c7
-- title:
--   Remark after Theorem 1, p. 910 — if r⁰ + r′ζ ⩽ 0 on 𝒱, the worst case is 0, attained in (21) at s = 0
-- statement:
--   This is the second case of the Remark after Theorem 1 of Goh and Sim (2010).
--
--   Let $\mathcal V, \widehat{\mathcal V} \subseteq \mathbb R^n$ with $\widehat{\mathcal V}$ nonempty and $\widehat{\mathcal V} \subseteq \mathcal V$, and let $\mathbb F_1$ be the family of distributions with integrable coordinates, mean in $\widehat{\mathcal V}$ and support in $\mathcal V$. Let $r^0 \in \mathbb R$, $r \in \mathbb R^n$ satisfy $r^0 + r'\zeta \le 0$ for all $\zeta \in \mathcal V$. Then
--   $$\sup_{\mathbb P \in \mathbb F_1} \mathbb E_{\mathbb P}\big((r^0 + r'\tilde\zeta)^+\big) = 0,$$
--   and the infimum defining $\pi^1(r^0, r)$ in (21) is attained at $s = 0$: writing $\Phi(s)$ for the objective of (21),
--   $$\Phi(0) = \pi^1(r^0, r) = 0.$$
--
--   When the affine function is nonpositive on the support, the positive part vanishes almost surely and both the worst case and the bound are zero.
--
--   **Formalization Note** The page states the implication with no condition on the sets; when $\mathbb F_1 = \emptyset$ the left side would be $-\infty$. As in the first case of the Remark, $\widehat{\mathcal V} \subseteq \mathcal V$ (the paper's construction, §4.5) and $\widehat{\mathcal V} \ne \emptyset$ are hypotheses; together they make $\mathbb F_1$ nonempty. Values are in `EReal`; $\Phi$ is `pi1Obj`.
-- source:
--   Goh & Sim, Distributionally Robust Optimization and Its Tractable Approximations, Oper. Res. 58(4), 2010, p. 910, Remark after Theorem 1 (second implication)

import Mathlib
import Definitions.Def_TractableDRO_MeanSupport_Model

open MeasureTheory

namespace TractableDRO.MeanSupport

theorem remark_nonpos {n : ℕ} (V Vhat : Set (Fin n → ℝ)) (hsub : Vhat ⊆ V)
    (hne : Vhat.Nonempty) (r0 : ℝ) (r : Fin n → ℝ) (hnp : ∀ ζ ∈ V, r0 + r ⬝ᵥ ζ ≤ 0) :
    worstCase (family1 V Vhat) r0 r = 0 ∧
      pi1Obj V Vhat r0 r 0 = pi1 V Vhat r0 r ∧ pi1 V Vhat r0 r = 0 := by sorry

end TractableDRO.MeanSupport
