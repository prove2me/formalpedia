-- Prove2me | Theorems.Thm_SubmodSparsify_claim_4_6
-- name    : SubmodSparsify.claim_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:22.143622+00:00
-- url     : https://prove2.me/theorems/e19b4180-76b2-4d28-8c9c-b598e034cf93
-- title:
--   Claim 4.6 — total influence budget (P2): $\sum_w \inf_S(w) \le 2F(S)$
-- statement:
--   Let $f_1, \dots, f_m : 2^{[n]} \to \mathbb R_{\ge 0}$ be submodular with $f_i(\emptyset) = f_i([n]) = 0$, $F := \sum_i f_i$, and let $\inf_S$ be the influences (25). For every query $S \subseteq [n]$,
--
--   $$\sum_{w \in S} \inf_S(w) \le F(S), \qquad \sum_{w \in \bar S} \inf_S(w) \le F(S), \qquad \text{hence} \qquad \sum_{w \in [n]} \inf_S(w) \le 2F(S).$$
--
--   This is property (P2) of the chaining framework: the influences of a query are paid for by its value.
--
--   Differences from the source:
--   - encoding: ground set [n] = {1, …, n}, subsets of [n], components f_1, …, f_m → Fin n (paper index = value + 1), Finset (Fin n), f : Fin m → Finset (Fin n) → ℝ; reason: Lean representation; same instances
--   - encoding: standing assumption of §4 (p.18): every component normalized, f_i(∅) = f_i([n]) = 0, nonnegative submodular → explicit hypotheses hf0, hsub, hempty, huniv; reason: the section's standing hypotheses written as binders; same instances
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), Claim 4.6, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubmodSparsify_weights

namespace SubmodSparsify

/-- **Claim 4.6** (p.25): the total influence budget (P2).

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Claim 4.6, p.25.

For every query `S ⊆ [n]`, `Σ_{w∈S} inf_S(w) ≤ F(S)` and `Σ_{w∈S̄} inf_S(w) ≤ F(S)`, and hence
`Σ_{w∈[n]} inf_S(w) ≤ 2F(S)`, where `F = Σᵢ fᵢ`.

**Formalization Note.** `[n]` is `Fin n`, components `f : Fin m → Finset (Fin n) → ℝ`
(paper indices = values + 1), `S̄ = Sᶜ`. The hypotheses on `f` are those of Theorem 4.1, the
standing assumption of §4 (p.18): nonnegative, submodular, `fᵢ(∅) = fᵢ([n]) = 0`. `inShare f u i`
is `s_i^{(u)}`, `outShare f v i` is `t_i^{(v)}`, `weights f i` is `pᵢ`, `influence f S w` is
`inf_S(w)` of (25), `residual f i S U` is `Δᵢ(S, U)` of (24) (module `SubmodSparsify.weights`). -/
theorem claim_4_6 {n m : ℕ} (f : Fin m → Finset (Fin n) → ℝ) (hf0 : ∀ i S, 0 ≤ f i S)
    (hsub : ∀ i, NonmonotoneSubmod.Shared.Submodular (f i))
    (hempty : ∀ i, f i ∅ = 0) (huniv : ∀ i, f i Finset.univ = 0)
    (S : Finset (Fin n)) :
    ∑ w ∈ S, influence f S w ≤ ∑ i, f i S ∧
    ∑ w ∈ Sᶜ, influence f S w ≤ ∑ i, f i S ∧
    ∑ w, influence f S w ≤ 2 * ∑ i, f i S := by sorry

end SubmodSparsify
