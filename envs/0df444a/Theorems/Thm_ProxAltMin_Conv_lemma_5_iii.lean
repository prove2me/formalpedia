-- Prove2me | Theorems.Thm_ProxAltMin_Conv_lemma_5_iii
-- name    : ProxAltMin.Conv.lemma_5_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:45.075482+00:00
-- url     : https://prove2.me/theorems/145203a9-afd9-4a9c-9e00-9bb3027900ba
-- title:
--   Lemma 5 (iii) — (x*ₖ, y*ₖ) ∈ ∂L(xₖ, yₖ) (8), and it tends to 0 along bounded subsequences
-- statement:
--   Let $L=f+Q+g$ satisfy (H) and (H1), and let $(x_k,y_k)$ comply with (5)–(6) with step sizes $\lambda_k,\mu_k$. For $k\ge1$ define
--   $$(x_k^*,y_k^*)=\big(\nabla_xQ(x_k,y_k)-\nabla_xQ(x_k,y_{k-1}),0\big)-\Big(\frac1{\lambda_{k-1}}(x_k-x_{k-1}),\ \frac1{\mu_{k-1}}(y_k-y_{k-1})\Big).$$
--   Then:
--   1. $(x_k^*,y_k^*)\in\partial L(x_k,y_k)$ for every $k\ge1$ (8), where $\partial$ is the limiting subdifferential;
--   2. for every bounded subsequence $(x_{k'},y_{k'})$ of $(x_k,y_k)$, $(x_{k'}^*,y_{k'}^*)\to0$ as $k'\to+\infty$, hence $\operatorname{dist}(0,\partial L(x_{k'},y_{k'}))\to0$.
--
--   The explicit subgradient $(x_k^*,y_k^*)$ is the bridge between the scheme and the Kurdyka–Łojasiewicz inequality.
--
--   **Formalization Note** A subsequence is $k'=\varphi(j)$ with $\varphi$ strictly increasing. "$\operatorname{dist}(0,\partial L(z_{k'}))\to0$" is written as: for every $\varepsilon>0$, eventually some $v\in\partial L(z_{k'})$ has $\|v\|<\varepsilon$ (this avoids the value $0$ that a library distance to an empty set would return).
-- source:
--   Attouch, Bolte, Redont, Soubeyran, Proximal alternating minimization and projection methods for nonconvex problems, Math. Oper. Res. (2010), p. 6, Lemma 5 (iii), (8)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_ProxAltMin_Conv_Setting
open NonconvexSplitting.Shared
open Filter Topology

namespace ProxAltMin.Conv

/-- Lemma 5 (iii) (p. 6): for every run of (5)–(6) under (H), (H1), the vector
`(x*ₖ, y*ₖ) = (∇ₓQ(xₖ, yₖ) - ∇ₓQ(xₖ, y_{k-1}), 0) - ((xₖ - x_{k-1}) / λ_{k-1}, (yₖ - y_{k-1}) / μ_{k-1})`
lies in `∂L(xₖ, yₖ)` for every `k ≥ 1` (8); and along every bounded subsequence `(x_{φ(j)}, y_{φ(j)})`,
`(x*_{φ(j)}, y*_{φ(j)}) → 0`, hence `dist(0, ∂L(x_{φ(j)}, y_{φ(j)})) → 0`. -/
theorem lemma_5_iii {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (Q : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (lam mu : ℕ → ℝ) (rm rp : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin m))
    (hH : AssumptionH f Q g) (hH1 : AssumptionH1 f Q g lam mu (y 0) rm rp)
    (hrun : IsPAMRun f Q g lam mu x y) :
    (∀ k : ℕ, 1 ≤ k → zstar Q lam mu x y k ∈ LimitingSubdiff (L f Q g) (pt (x k) (y k))) ∧
    ∀ φ : ℕ → ℕ, StrictMono φ →
      Bornology.IsBounded (Set.range (fun j => pt (x (φ j)) (y (φ j)))) →
        Tendsto (fun j => zstar Q lam mu x y (φ j)) atTop (𝓝 0) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
          ∃ v ∈ LimitingSubdiff (L f Q g) (pt (x (φ j)) (y (φ j))), ‖v‖ < ε := by sorry

end ProxAltMin.Conv
