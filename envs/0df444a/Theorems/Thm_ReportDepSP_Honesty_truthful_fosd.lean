-- Prove2me | Theorems.Thm_ReportDepSP_Honesty_truthful_fosd
-- name    : ReportDepSP.Honesty.truthful_fosd
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:50.121008+00:00
-- url     : https://prove2.me/theorems/806a2c8d-729d-40fd-97c5-7bb9cfee5bdd
-- title:
--   Proof of Proposition 2, p. 12 — the true lottery first-order stochastically dominates that of any ROL R̃
-- statement:
--   Let $P \ge 0$ be a nonnegative weight function on attainability states and $\widetilde R$ any ROL. Options are labelled $1,\dots,n$ from best to worst. For every $k \in ⟦1,n⟧$, the probability of being matched with one of the options $1,\dots,k$ is at least as large under the true ROL as under $\widetilde R$:
--   $$\sum_{s=1}^{k} \widetilde f_{\widetilde R(s)} \ \le\ \sum_{s=1}^{k} f_s \qquad \forall k\in⟦1,n⟧ .$$
--
--   In words, the lottery over options induced by truthful reporting first-order stochastically dominates the lottery induced by any other list, with respect to the ordering $1 \succ 2 \succ \dots \succ n$. The paper invokes this as the consequence of strategy-proofness that makes $\Delta_v$ nonnegative; in the model it is a property of the matching rule "matched with the highest-ranked attainable option".
--
--   **Formalization Note** Options are 0-indexed: `Iic k` with `k : Fin n` is the page's set $\{1,\dots,k+1\}$. Only nonnegativity of $P$ is assumed. The page states this as a justification ("strategy-proofness implies a first-order stochastic dominance of the true lottery"); the Lean states it as a theorem about the model's match probabilities.
-- source:
--   Meisner, Report-dependent utility and strategy-proofness, CRC TRR 190 Discussion Paper No. 289 (2021; Management Science doi:10.1287/mnsc.2022.4504), proof of Proposition 2 (Appendix), p. 12, "strategy-proofness implies a first-order stochastic dominance of the true lottery"

import Mathlib
import Definitions.Def_ReportDepSP_Honesty_Setting

namespace ReportDepSP.Honesty

open Finset

/-- Proof of Proposition 2 (p. 12): first-order stochastic dominance of the true lottery. For
every `k`, the probability of being matched with one of the options `0, …, k` (the `k + 1` best by
`v`) is at least as large under the true ROL `1` as under any ROL `Rt`. -/
theorem truthful_fosd {n : ℕ} (P : (Fin n → Bool) → ℝ) (Rt : Equiv.Perm (Fin n))
    (hP0 : ∀ a, 0 ≤ P a) :
    ∀ k : Fin n, ∑ s ∈ Iic k, matchProb P Rt (Rt s) ≤ ∑ s ∈ Iic k, matchProb P 1 s := by sorry

end ReportDepSP.Honesty
