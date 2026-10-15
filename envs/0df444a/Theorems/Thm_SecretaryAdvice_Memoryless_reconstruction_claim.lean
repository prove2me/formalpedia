-- Prove2me | Theorems.Thm_SecretaryAdvice_Memoryless_reconstruction_claim
-- name    : SecretaryAdvice.Memoryless.reconstruction_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:56.920929+00:00
-- url     : https://prove2.me/theorems/3e0bd5e8-7a94-4ae9-841c-3f02b4dcfe77
-- title:
--   Proof of Proposition 10, p. 11 — under the reconstructed policy (6), P[i is picked | T_i, s_i = s] = z(i,s)
-- statement:
--   Let $\mathbb P$ be a signaling structure satisfying Non-Filtering and History-Irrelevance, and let $z(i,s)\ge 0$ satisfy constraint (4). Let $q$ be the reconstructed policy (6): at a best-so-far round $i$ with signal $s$ it stops with probability
--   $$q(i,s)=\frac{z(i,s)}{1-\sum_{j<i}\sum_{s'\in\mathcal S} z(j,s')\,\mathbb P[T_j,\ s_j=s'\mid T_i,\ s_i=s]},$$
--   and it never stops at a round that is not best so far. Then for every $i$ and $s$,
--   $$\mathbb P[i\text{ is picked}\mid T_i,\ s_i=s]=z(i,s).$$
--
--   This is the claim established at the start of the proof of Proposition 10; combined with equation (3) it gives that the policy's success probability equals the objective (5).
--
--   **Formalization Note** Secretaries are indexed by `Fin n`, 0-based: Lean index $i$ is the paper's secretary $i+1$, and Lean rank $r$ is the paper's rank $r+1$, so the paper's top rank $n$ is Lean rank $n-1$. The conditional equality is stated cross-multiplied, $\mathbb E[\mathbf 1\{T_i,s_i=s\}\cdot\mathbb P[i\text{ is picked}]]=z(i,s)\cdot\mathbb P[T_i,s_i=s]$. The policy (6) is set to $0$ when its denominator vanishes (feasibility then forces $z(i,s)=0$).
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 11, proof of Proposition 10, first claim ("Before we do that, we show that under the reconstructed policy …")

import Mathlib
import Definitions.Def_SecretaryAdvice_Memoryless_Setting
import Definitions.Def_SecretaryAdvice_Memoryless_LP

namespace SecretaryAdvice.Memoryless

/-- Proof of Proposition 10, p. 11: under the reconstructed policy (6),
`P[i is picked | T_i, s_i = s] = z(i, s)`, cross-multiplied. -/
theorem reconstruction_claim {n : ℕ} {S : Type} [Fintype S] (μ : SignalingStructure n S)
    (hNF : NonFiltering μ) (hHI : HistoryIrrelevance μ) (z : Fin n → S → ℝ)
    (hz : LPFeasible μ z) (i : Fin n) (s : S) :
    expectOn μ (pickProb (reconstructedPolicy μ z) i) (fun ω => T i ω ∧ sig i ω = s) =
      z i s * prob μ (fun ω => T i ω ∧ sig i ω = s) := by sorry

end SecretaryAdvice.Memoryless
