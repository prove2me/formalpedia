-- Prove2me | Theorems.Thm_PermBlockchain_Transfers_lemma_B_1_b
-- name    : PermBlockchain.Transfers.lemma_B_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:22.011259+00:00
-- url     : https://prove2.me/theorems/feffa824-bad5-4bae-8cd8-d273af6d2f1f
-- title:
--   Lemma B.1(b), p. 38 — for large Δ there is φ* ≥ 0 with h(φ*; φ*) = 0, and consumers pay iff φ_k ≤ φ*
-- statement:
--   Fix the model of the Setting, and let $h(\phi_k;\phi)$ be the gain from paying the access fee $\kappa=\sum_{i\in M}\chi_i/G(\phi)$ for a consumer with outside option $\phi_k$, as in Lemma B.1(a). There is $\Delta_0$ such that for every $\Delta>\Delta_0$ there exists $\phi^*\ge 0$ with
--   1. $h(\phi^*;\phi^*)=0$;
--   2. for every $\phi_k\ge 0$, $h(\phi_k;\phi^*)\ge 0$ if and only if $\phi_k\le\phi^*$;
--   3. consequently, at the fee $\kappa=\sum_{i\in M}\chi_i/G(\phi^*)$, a consumer with outside option $\phi_k\ge 0$ pays for access ($b_k=1$) if and only if $\phi_k\le\phi^*$.
--
--   The threshold $\phi^*$ is a fixed point: it is the outside-option value at which the marginal consumer is indifferent when the fee is calibrated to the mass $G(\phi^*)$ of consumers below it. It is the key step in the proof of Proposition 4.9.
--
--   **Formalization Note** The lemma's final sentence ("$\phi^*$ is not necessarily unique with a general cumulative distribution function $G$") is an example claim, illustrated by the paper's Example B.1, and is not formalized. Clause 3 is the paper's "Therefore, $b_k=1$ if and only if $\phi_k\le\phi^*$", stated through the set of paying consumers of the Setting. No positivity of $G(\phi^*)$ is assumed: Lean's value $0$ for a division by $G(\phi^*)=0$ cannot satisfy clauses 1 and 2 together.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), p. 38, Lemma B.1(b)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_Setting

namespace PermBlockchain.Transfers
theorem lemma_B_1_b {m : ℕ} (M : Model m) (hM : M.Standing) :
    ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ < Δ → ∃ φs : ℝ, 0 ≤ φs ∧ M.hfun Δ φs φs = 0 ∧
      (∀ φk : ℝ, 0 ≤ φk → (0 ≤ M.hfun Δ φk φs ↔ φk ≤ φs)) ∧
      (∀ φk : ℝ, 0 ≤ φk → (φk ∈ M.payers Δ ((∑ i, M.χ i) / M.G φs) ↔ φk ≤ φs)) := by sorry
end PermBlockchain.Transfers
