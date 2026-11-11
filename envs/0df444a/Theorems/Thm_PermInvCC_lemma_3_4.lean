-- Prove2me | Theorems.Thm_PermInvCC_lemma_3_4
-- name    : PermInvCC.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:25:41.728194+00:00
-- url     : https://prove2.me/theorems/38b8a126-5dba-4e72-b47a-28b1f07c2ae1
-- title:
--   Lemma 3.4 — recovering the disagreement set with $O(B\log(n/B)+\log(1/\varepsilon))$ bits
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $n\ge2$, let $B$ be an integer with $1\le B\le n/2$, and let $\varepsilon\in(0,1)$. There is a public-coin protocol, with finite public randomness, in which Alice holds $\xi\in\mathbb F_2^n$ and Bob holds $\eta\in\mathbb F_2^n$, such that
--
--   1. the protocol either reports failure to both parties or gives both parties the same set $\hat D\subseteq[n]$ of size at most $B$;
--   2. if the disagreement set $D:=\{i:\xi_i\ne\eta_i\}$ has $|D|\le B$, then $\Pr[\hat D=D]\ge1-\varepsilon$;
--   3. for every input and every execution, the communication is at most $C\bigl(B\log(n/B)+\log(1/\varepsilon)\bigr)$ bits.
--
--   This batch recovery is the expensive step of the classical protocol of Theorem 3.1.
--
--   Differences from the source:
--   - encoding: O(B log(n/B) + log(1/ε)) bits → cost ≤ C(B log₂(n/B) + log₂(1/ε)) with one absolute C chosen before n, B, ε; reason: the O-constant is absolute
--   - encoding: reports failure / returns D̂ → output none / some D̂ of type Option (Finset (Fin n)); reason: Lean representation of the two outcomes
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Lemma 3.4, pp.11–12

import Mathlib
import Definitions.Def_PermInvCC_PubProtocol

namespace PermInvCC

/-- **Lemma 3.4 (Recovering the Disagreement Set)** (Y. Huang and Z. Ye, arXiv:2609.40116, held
version sha256 fe1797dd…, pp.11–12). Let `n ≥ 2`, let `B` be an integer with `1 ≤ B ≤ n/2`, and
let `ε ∈ (0, 1)`. There is a public-coin protocol in which Alice holds `ξ ∈ F₂ⁿ` and Bob holds
`η ∈ F₂ⁿ`, which either reports failure to both parties or gives both parties the same set
`D̂ ⊆ [n]` of size at most `B`. If the disagreement set `D = {i : ξ_i ≠ η_i}` has size at most
`B`, then `P[D̂ = D] ≥ 1 − ε`. For every input and every execution, the communication is at most
`O(B log(n/B) + log(1/ε))` bits. The protocol uses only finite public randomness.

**Formalization Note.** The output `none` is "failure"; `some D̂` returns `D̂`. The `O(·)` is one
absolute constant `C` chosen before `n, B, ε`. "Size at most `B`" holds for every input and coin
value; the cost is the worst case over all inputs and coins. Public randomness is finite by the
definition of `PubProtocol`. -/
theorem lemma_3_4 :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ B : ℕ, 1 ≤ B → 2 * B ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ P : PubProtocol (Fin n → ZMod 2) (Fin n → ZMod 2) (Option (Finset (Fin n))),
        (∀ ω ξ η D, P.run ω ξ η = some D → D.card ≤ B) ∧
        (∀ ξ η : Fin n → ZMod 2, (Finset.univ.filter fun i => ξ i ≠ η i).card ≤ B →
          1 - ε ≤ P.prob ξ η (fun o => o = some (Finset.univ.filter fun i => ξ i ≠ η i))) ∧
        (P.cost : ℝ) ≤ C * (B * Real.logb 2 ((n : ℝ) / B) + Real.logb 2 (1 / ε)) := by sorry

end PermInvCC
