-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_lemma_7
-- name    : STPRideshare.Mechanism.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:41.185666+00:00
-- url     : https://prove2.me/theorems/1b4575a5-2a9c-4b5f-9a1c-ab634750c759
-- title:
--   Lemma 7, p. 43 — optimal solutions of the dual LP (15) and of the dual (41) of the flow LP correspond
-- statement:
--   Let $E$ be a valid economy. The dual LP (15) of (9) is: minimize $\sum_i\pi_i+\sum_ju_j$ over prices $p$, driver variables $\pi$ and rider variables $u$, subject to (16) $\pi_i\ge\sum_{(a,b,t)\in Z}p_{a,b,t}-\lambda_i(Z)$ for every feasible path $Z$ of driver $i$, (17) $u_j\ge v_j-p_{o_j,d_j,\tau_j}$, (18) $p\ge0$ on $\mathcal T$, (19) $u\ge0$. The dual (41) of the flow LP is: minimize $\sum_i\phi_{D_i}+\sum_j\mu_j$ over node potentials $\phi_{a,t}$ ($t\le T$), driver potentials $\phi_{D_i}$ and $\mu$, subject to
--   $$\phi_{o_j,\tau_j}-\phi_{d_j,\tau_j+\delta(o_j,d_j)}+\mu_j\ge v_j-c_{o_j,d_j,\tau_j},\quad \phi_{a,t}-\phi_{b,t+\delta(a,b)}\ge-c_{a,b,t}\ \ ((a,b,t)\in\mathcal T),\quad \phi_{a,t}\ge-\kappa_{T-t},$$
--   $$\phi_{D_i}\ge\phi_{\ell_i,\tau_i},\quad \phi_{D_i}\ge0 \text{ if }\beta_i=0,\quad \mu_j\ge0 .$$
--
--   Then for every optimal solution $(p,\pi,u)$ of (15) there is an optimal solution $(\phi,\mu)$ of (41) with $\phi_{D_i}=\pi_i$ for all $i$ and $\mu_j=u_j$ for all $j$; and conversely, for every optimal $(\phi,\mu)$ of (41) there is an optimal $(p,\pi,u)$ of (15) with $\pi_i=\phi_{D_i}$ and $u_j=\mu_j$.
--
--   The correspondence transfers the lattice structure of optimal flow potentials to CE driver utilities (Lemma 4) and is used in Step 1 of the proof of Theorem 2.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 43, Lemma 7 (Appendix B.4), dual LPs (15)–(19) p. 14 and (41)–(47) p. 42

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_Model

namespace STPRideshare.Mechanism

/-- Lemma 7, p. 43: optimal solutions of the dual LP (15) and of the dual (41) of the flow LP
correspond, with `ϕ_{D_i} = π_i` and `μ_j = u_j`, in both directions. -/
theorem lemma_7 {L ι κ : Type} [Fintype L] [Fintype ι] [Fintype κ] (e : Econ L ι κ)
    (he : e.Valid) :
    (∀ (p : Price L) (π : ι → ℝ) (u : κ → ℝ), e.DualOptimal p π u →
      ∃ (ϕ : L → ℕ → ℝ) (ϕD : ι → ℝ) (μ : κ → ℝ), e.FlowDualOptimal ϕ ϕD μ ∧
        (∀ i, ϕD i = π i) ∧ (∀ j, μ j = u j)) ∧
    (∀ (ϕ : L → ℕ → ℝ) (ϕD : ι → ℝ) (μ : κ → ℝ), e.FlowDualOptimal ϕ ϕD μ →
      ∃ (p : Price L) (π : ι → ℝ) (u : κ → ℝ), e.DualOptimal p π u ∧
        (∀ i, π i = ϕD i) ∧ (∀ j, u j = μ j)) := by sorry

end STPRideshare.Mechanism
