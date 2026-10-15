-- Prove2me | Theorems.Thm_PermBlockchain_Transfers_lemma_B_1_a
-- name    : PermBlockchain.Transfers.lemma_B_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:25.200586+00:00
-- url     : https://prove2.me/theorems/c3bd0bf2-7603-466e-ad15-06851b9c7e3e
-- title:
--   Lemma B.1(a), p. 38 — h(φ_k; φ) is continuous and weakly decreasing in φ_k on [0, ∞)
-- statement:
--   Fix the model of the Setting and a degree of horizontal differentiation $\Delta>0$ (that is, $H>L$). For every $\phi$, consider the difference between a consumer's objective with and without access to the blockchain at the fee $\kappa=\sum_{i\in M}\chi_i/G(\phi)$,
--   $$h(\phi_k;\phi)=\max\{\Delta+L+h-\gamma,\phi_k\}-\frac{\sum_{i\in M}\chi_i}{G(\phi)}-\max\Big\{\frac{\Delta}{2}+L+h-\gamma,\phi_k\Big\}.$$
--   Then, as a function of the outside option $\phi_k$, $h(\phi_k;\phi)$ is continuous and weakly decreasing on $[0,\infty)$.
--
--   This is the shape property behind the threshold structure of the consumers' access decision: consumers with low outside options gain most from access.
--
--   **Formalization Note** The paper states the lemma for every $\phi$; when $G(\phi)=0$ the paper's expression is undefined and Lean reads the quotient as $0$, which leaves the statement true. The hypothesis $\Delta>0$ is the model's standing assumption $L<H$; for $\Delta<0$ the function would increase on part of $[0,\infty)$.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), p. 38, Lemma B.1(a)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_Setting

namespace PermBlockchain.Transfers
theorem lemma_B_1_a {m : ℕ} (M : Model m) (hM : M.Standing) (Δ : ℝ) (hΔ : 0 < Δ) (φ : ℝ) :
    ContinuousOn (fun φk => M.hfun Δ φk φ) (Set.Ici 0) ∧
      AntitoneOn (fun φk => M.hfun Δ φk φ) (Set.Ici 0) := by sorry
end PermBlockchain.Transfers
