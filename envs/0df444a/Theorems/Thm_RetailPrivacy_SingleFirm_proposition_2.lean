-- Prove2me | Theorems.Thm_RetailPrivacy_SingleFirm_proposition_2
-- name    : RetailPrivacy.SingleFirm.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:13:31.942412+00:00
-- url     : https://prove2.me/theorems/f08a3802-282c-45b4-904e-628796ffe349
-- title:
--   Proposition 2, p. 16 — the ℂ-mode equilibrium: ℓ̃* = 1, and (p̃*, 𝒯₂(p̃*)) on v ≤ 2(1−δ) and v > 2(1−δ)
-- statement:
--   Let $c>0$, $\delta\in(0,1)$, $v>0$. Under the $\mathbb C$ mode (the GDPR) the single-firm game has a subgame-perfect equilibrium, and in every subgame-perfect equilibrium the firm collects data ($\tilde\ell^*=1$), and its on-path price $\tilde p^*$ and sales quantity $\mathcal T_2(\tilde p^*)$ are
--   $$(\tilde p^*,\mathcal T_2(\tilde p^*)) = \begin{cases} \left(\dfrac v2,\ \dfrac{v}{2(1-\delta)}\right) & \text{if } v\le 2(1-\delta),\\[3mm] \left(v-(1-\delta),\ 1\right) & \text{if } v> 2(1-\delta).\end{cases}$$
--   Here $\mathcal T_2(p)$ is the demand at price $p$ with collection and no exploitation ($r=0$).
--
--   **Formalization Note** As in Proposition 1, prices range over $\mathbb R$, the subgame $\ell=0$ is part of the profile, and $v>0$ is an added (implicit) assumption.
-- source:
--   Xu, Wang & Zhang, Consumer Privacy in Online Retail Supply Chains, author manuscript (Management Science, forthcoming; version of November 2024), p. 16, Proposition 2; proof pp. ec22–ec23

import Mathlib
import Definitions.Def_RetailPrivacy_SingleFirm_Model

namespace RetailPrivacy.SingleFirm

theorem proposition_2 (c δ v : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v) :
    (∃ P : Profile, IsSPE .C v c δ P) ∧
    ∀ P : Profile, IsSPE .C v c δ P →
      P.collect = true ∧
      (v ≤ 2 * (1 - δ) →
        eqPrice P = v / 2 ∧ demand true v δ (eqPrice P) 0 = v / (2 * (1 - δ))) ∧
      (2 * (1 - δ) < v →
        eqPrice P = v - (1 - δ) ∧ demand true v δ (eqPrice P) 0 = 1) := by sorry

end RetailPrivacy.SingleFirm
