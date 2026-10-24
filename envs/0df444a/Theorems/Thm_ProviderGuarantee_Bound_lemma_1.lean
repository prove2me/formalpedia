-- Prove2me | Theorems.Thm_ProviderGuarantee_Bound_lemma_1
-- name    : ProviderGuarantee.Bound.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:26.823522+00:00
-- url     : https://prove2.me/theorems/a79f8fdc-13fd-48e4-bd98-f448c06144e5
-- title:
--   Lemma 1, p. 35 — for A ∈ F* and B ∈ F*_G, v(A_i ∖ (B_1 ∪ … ∪ B_n)) ≤ v(B_j ∖ A_i) for all i, j
-- statement:
--   Throughout, $D$ is a finite set of jobs with real values $v : D \to \mathbb R$ and $v(S) = \sum_{d \in S} v(d)$; there are $n$ providers $N = \{1, \dots, n\}$; $0 < \gamma_{\min} \le \gamma_{\max}$ and $\gamma \in [\gamma_{\min}, \gamma_{\max}]^n$; $\mathcal F$ is a set of allocations $A = (A_1, \dots, A_n)$ satisfying Assumption 1, and $\mathcal F_G \subseteq \mathcal F$ satisfies Assumption 2. The optimal sets are $\mathcal F^* = \arg\max_{A \in \mathcal F} \sum_i \gamma_i v(A_i)$ and $\mathcal F_G^* = \arg\max_{B \in \mathcal F_G} \sum_i \gamma_i v(B_i)$.
--
--   **Lemma 1.** Let $A \in \mathcal F^*$ and $B \in \mathcal F_G^*$. Then
--
--   $$v\big(A_i \setminus (B_1 \cup \dots \cup B_n)\big) \le v(B_j \setminus A_i) \qquad \text{for all } i, j \in N. \qquad (10)$$
--
--   This optimality condition says that the jobs an optimal unrestricted allocation gives to provider $i$, and which no optimal guaranteed allocation uses, are worth no more than what any provider $j$ holds outside $A_i$ in the guaranteed optimum. It is the only place where the structure of $\mathcal F$ and $\mathcal F_G$ enters the proof of Theorem 1.
--
--   **Formalization Note** $\mathcal F^*$ and $\mathcal F_G^*$ are expressed by `IsOptimal`: membership plus maximality of the total value.
--
--   Differences from the source:
--   - reading: Lemma 1 is stated 'for any fixed F and F_G' → F satisfies Assumption 1, F_G ⊆ F satisfies Assumption 2, and γ ∈ [γmin, γmax]^n with 0 < γmin ≤ γmax; reason: these are the standing assumptions of §2 (pp. 7–12) under which the appendix works; the proof on pp. 35–36 uses Assumption 1-(ii), (iii), (iv), Assumption 2 and γ_j > 0, and the lemma is false without them
--   - reading: a set of jobs D (never said to be finite; v(S) is a finite sum and maxima over F are taken) → D a finite type; reason: the page writes v(S) = Σ_{d∈S} v(d) and max over F, which presuppose finitely many jobs; the paper calls D a discrete set of jobs
--   - encoding: providers N = {1, …, n} → indices i : Fin n (0, …, n−1); reason: Lean convention; a relabelling, same instances
-- source:
--   Gur, Iancu & Warnes, Value Loss in Allocation Systems with Provider Guarantees, SSRN 3351509 (version of March 24, 2020), p. 35, Lemma 1, (10)

import Mathlib
import Definitions.Def_ProviderGuarantee_Bound_Model

namespace ProviderGuarantee.Bound

theorem lemma_1 {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} (v : D → ℝ)
    (γmin γmax : ℝ) (hγmin : 0 < γmin) (hγ : γmin ≤ γmax)
    (γ : Fin n → ℝ) (hγmem : ∀ i, γ i ∈ Set.Icc γmin γmax)
    (F FG : Set (Fin n → Finset D)) (h1 : Assumption1 F) (h2 : Assumption2 v F FG)
    (A B : Fin n → Finset D) (hA : IsOptimal γ v F A) (hB : IsOptimal γ v FG B) :
    ∀ i j, val v (A i \ Finset.univ.biUnion B) ≤ val v (B j \ A i) := by sorry

end ProviderGuarantee.Bound
