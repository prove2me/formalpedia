-- Prove2me | Theorems.Thm_QualityEncroach_Differ_quantity_subgame
-- name    : QualityEncroach.Differ.quantity_subgame
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:27:15.359545+00:00
-- url     : https://prove2.me/theorems/343a39a1-4352-4022-b351-d02247dbd7e3
-- title:
--   Eq. (7), p. 16 — equilibrium quantities q_R(w,u,t), q_M(w,u,t) of the quantity subgame for t < 1
-- statement:
--   Fix $k>0$, $c\ge0$, a wholesale price $w$, a direct quality $u>0$ and a ratio $0<t<1$, so that the retailer sells the lower quality $tu$. Let $q_R(w,u,t)$ and $q_M(w,u,t)$ be the quantities of (7):
--
--   $$
--   q_R(w,u,t)=\frac{1}{2(2-t)}-\frac{w}{t(2-t)u}+\frac{ku}{2(2-t)}+\frac{c}{2(2-t)u},\qquad
--   q_M(w,u,t)=\frac{4-3t}{4(2-t)}+\frac{w}{2(2-t)u}-\frac{(4-t)ku}{4(2-t)}-\frac{(4-t)c}{4(2-t)u}.
--   $$
--
--   Suppose both are nonnegative. Then they are the equilibrium quantities of the subgame that starts after $(w,u,t)$:
--
--   1. $q_M(w,u,t)$ maximizes the manufacturer's profit $\Pi_M$ over $q_M\ge 0$ when the retailer has ordered $q_R(w,u,t)$;
--   2. for every order $q_R\ge0$ and every best response $q_M\ge 0$ of the manufacturer to $q_R$ (a maximizer of $\Pi_M$ over $q_M\ge0$), the retailer's profit at $(q_R,q_M)$ is at most his profit at $(q_R(w,u,t),q_M(w,u,t))$.
--
--   This is the first step of the backward induction for high-quality encroachment; the manufacturer's choice of $w$ given $(t,u)$ is computed from these quantities in the proof of Lemma 1(i).
--
--   **Formalization Note.** The paper states (7) without a region; the hypotheses $q_R(w,u,t)\ge0$ and $q_M(w,u,t)\ge0$ are the region in which the closed forms are the equilibrium quantities with nonnegative quantities.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 16, eq. (7)

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Game
import Definitions.Def_QualityEncroach_Differ_Reduced

namespace QualityEncroach.Differ

theorem quantity_subgame (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (w u t : ℝ) (hu : 0 < u)
    (ht0 : 0 < t) (ht1 : t < 1) (hqR : 0 ≤ qR7 k c w u t) (hqM : 0 ≤ qM7 k c w u t) :
    (∀ qM : ℝ, 0 ≤ qM →
      mfrPayoff k c ⟨w, u, t, qR7 k c w u t, qM⟩ ≤
        mfrPayoff k c ⟨w, u, t, qR7 k c w u t, qM7 k c w u t⟩) ∧
    (∀ qR qM : ℝ, 0 ≤ qR → 0 ≤ qM →
      (∀ qM' : ℝ, 0 ≤ qM' → mfrPayoff k c ⟨w, u, t, qR, qM'⟩ ≤ mfrPayoff k c ⟨w, u, t, qR, qM⟩) →
      retailerPayoff ⟨w, u, t, qR, qM⟩ ≤
        retailerPayoff ⟨w, u, t, qR7 k c w u t, qM7 k c w u t⟩) := by sorry

end QualityEncroach.Differ
