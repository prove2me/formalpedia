-- Prove2me | Theorems.Thm_VaccineAMC_Framework_proposition_2
-- name    : VaccineAMC.Framework.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:27.947978+00:00
-- url     : https://prove2.me/theorems/cee4c8ce-b9d9-4ab5-967e-b8e382ccae30
-- title:
--   Proposition 2 — no-AMC equilibrium and hold-up
-- statement:
--   Under the standing assumptions and Assumption 1, the no-AMC capacity game has the unique equilibrium $Q^{\mathrm{NA}}=q^{\mathrm{NA}}=D(c+\kappa/\beta)$. At that capacity, the firm's ex ante value is $\pi(Q^{\mathrm{NA}},\theta)$, where $\pi(Q,\theta)=(\beta/r)[\alpha B(Q)-(c+\kappa/\beta)Q]$. Moreover,
--
--   $$Q^{\mathrm{NA}}<Q^{\mathrm{IN}},\qquad \lim_{\beta\to0^+}Q^{\mathrm{NA}}=0,\qquad \lim_{\beta\to1^-}Q^{\mathrm{NA}}=Q^{\mathrm{IN}}.$$
--
--   The comparison quantifies underinvestment when the firm shares the returns from a sunk capacity cost. **Formalization Note** In the endpoint limits, $\beta$ varies while the other model parameters remain fixed.
-- source:
--   Kremer, Levin & Snyder, Designing Advance Market Commitments for New Vaccines, BFI Working Paper No. 2020-175 (Dec. 2020), p. 11 (PDF 14), Proposition 2

import Mathlib
import Definitions.Def_VaccineAMC_Framework_Model

open Filter Topology

namespace VaccineAMC.Framework

theorem proposition_2 (θ : Params) (hS : θ.Standing) (hA1 : Assumption1 θ) :
    (∀ Q q : ℝ, IsEqNA θ Q q ↔
      Q = demand θ (θ.c + θ.κ / θ.β) ∧ q = Q) ∧
    firmValueNA θ (demand θ (θ.c + θ.κ / θ.β)) =
      profitNA θ (demand θ (θ.c + θ.κ / θ.β)) ∧
    demand θ (θ.c + θ.κ / θ.β) < demand θ (θ.c + θ.κ) ∧
    Tendsto (fun b : ℝ => demand θ (θ.c + θ.κ / b)) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun b : ℝ => demand θ (θ.c + θ.κ / b)) (𝓝[<] 1)
      (𝓝 (demand θ (θ.c + θ.κ))) := by sorry

end VaccineAMC.Framework
