-- Prove2me | Theorems.Thm_ProcFlex_DMGI_proposition_1
-- name    : ProcFlex.DMGI.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:19.585548+00:00
-- url     : https://prove2.me/theorems/4c826b4f-c10a-4cfb-929d-043a136e2cd8
-- title:
--   Proposition 1: alternate-chain DMGI dominance
-- statement:
--   In a balanced $2k$-plant, $2k$-product system with unit capacities and $k$ products at each of two margins, compare any long chain $L_{HL}$ with any alternate long chain $\mathrm{AL}$. For every feasible parameter set $K\in Q$,
--
--   $$
--   \delta^K(\mathrm{AL})\ge\delta^K(L_{HL}).
--   $$
--
--   Together with Theorem 2(a), this gives the robust-score comparison in Theorem 3.
--
--   **Formalization Note** The fixed products are permuted along the cycle, preserving the same margin categories. The homogeneous DMGI uses $\mu=0$, unit capacities, and the paper's intended $z\ge0$ constraint.
-- source:
--   Wang, Wang & Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 22 May 2020), p. 22, Proposition 1

import Mathlib
import Definitions.Def_ProcFlex_DMGI_Model

namespace ProcFlex.DMGI

/-- Proposition 1, p. 22: every feasible homogeneous DMGI is at least as
large on an alternate chain as on any other long chain. -/
theorem proposition_1 (k : ℕ) (hk : 1 ≤ k)
    (S : System (2 * k) (2 * k) 2) (hS : S.IsValid)
    (hC : ∀ j, S.C j = 1) (hcard : (S.s 1).card = k)
    (πAL π : Equiv.Perm (Fin (2 * k))) (hAL : IsAlternate S πAL)
    (K : Fin 2 → Fin 3 → ℕ) (hK : InQ S K) :
    dmgi S 0 K (longChain π) ≤ dmgi S 0 K (longChain πAL) := by sorry

end ProcFlex.DMGI
