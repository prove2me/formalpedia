-- Prove2me | Theorems.Thm_SCInfoDesign_Disjoint_eq_B2
-- name    : SCInfoDesign.Disjoint.eq_B2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:51.223615+00:00
-- url     : https://prove2.me/theorems/514b89b0-60f8-4363-87cb-66b1400653c9
-- title:
--   App. B, p. 25, after (B.2) — with disjoint supports, the optimal value of (3) is the lower convex envelope κ_DS(p₀)
-- statement:
--   Consider the model with disjoint supports: $D_0\sim U[a_0,b_0]$, $D_1\sim U[a_1,b_1]$ with $a_0<b_0$, $a_1<b_1$, $0\le a_0$, $0\le a_1$, $b_1<a_0$, and $0<\xi<1$. Let $K_{DS}(p)$ be the retailer's expected shortage at belief $p$ when the supplier produces the largest of his optimal quantities, and let $\kappa_{DS}$ be the lower convex envelope of $K_{DS}$ on $[0,1]$, the greatest convex function on $[0,1]$ lying below $K_{DS}$ there.
--
--   For every prior $p_0\in[0,1]$, the infimum of the retailer's expected cost (3)
--   $$\sum_{m}\mathbb P(m)\,\Big(p_m\,\mathbb E[(D_0-Q^*(p_m))^+]+(1-p_m)\,\mathbb E[(D_1-Q^*(p_m))^+]\Big),$$
--   taken over all policies $\pi$ with a finite message space and all best-response profiles $Q^*$ of the supplier, equals $\kappa_{DS}(p_0)$:
--   $$\inf_{\Gamma,\ Q^*\in\mathcal B(\Gamma)}\ \mathbb E\big[\,p(D_0-Q^*_p)^++(1-p)(D_1-Q^*_p)^+\ \big|\ \Gamma\big]=\kappa_{DS}(p_0).$$
--   Here $p_m$ is the posterior (1) after message $m$.
--
--   This reduces the retailer's design problem to the computation of a convex envelope (Lemma 3), and is the first step of the proof of Theorem 3.
--
--   **Formalization Note** The statement is that $\kappa_{DS}(p_0)$ is the greatest lower bound of the set of attainable costs; message spaces are `Fin n`, which represent every finite message space up to relabelling. Unlike the nested case of p. 25, the supplier's best response is not unique at $p=1-\xi$; the claim holds because the retailer may choose the supplier's best response, and $K_{DS}$ is defined at the largest optimal quantity accordingly.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), App. B, p. 25, after (B.2); applied to disjoint supports in the proof of Theorem 3, p. 38

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Disjoint_Setting

namespace SCInfoDesign.Disjoint

open BiconvexProg.BranchBound

/-- The value claim after (B.2) (App. B, p. 25), for disjoint supports: the optimal value of the
design problem (3), over all finite-message policies and all best-response profiles, is the lower
convex envelope `κ_DS(p₀)` of `K_DS` on `[0, 1]`. -/
theorem eq_B2 (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hξ₀ : 0 < P.ξ) (hξ₁ : P.ξ < 1) (hdisj : P.b₁ < P.a₀)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0 : ℝ) 1) :
    IsGLB {c : ℝ | ∃ (n : ℕ) (π : Fin 2 → Fin n → ℝ) (Qs : ℝ → ℝ),
        SCInfoDesign.Nested.IsPolicy π ∧ P.IsBestResponseProfile Qs ∧ c = expectedCost P p₀ π Qs}
      (convexEnvelope (Set.Icc (0 : ℝ) 1) P.K p₀) := by sorry

end SCInfoDesign.Disjoint
