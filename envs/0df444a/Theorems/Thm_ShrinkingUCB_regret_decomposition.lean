-- Prove2me | Theorems.Thm_ShrinkingUCB_regret_decomposition
-- name    : ShrinkingUCB.regret_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:20:07.988172+00:00
-- url     : https://prove2.me/theorems/b471ce97-a023-481d-8f36-2ab59b22e569
-- title:
--   Regret decomposition, p.18 — $R(T)$ as a sum over the selections outside $S^*$
-- statement:
--   Let $K\le N$ and $|S^*|=K$. On every outcome table, the regret of period $t$ is
--
--   $$
--   \sum_{i\in S^*}\mu(i)-\sum_{i\in S_t}\mu(i)=\sum_{i\in S^*\setminus S_t}\mu(i)-\sum_{i\in S_t\setminus S^*}\mu(i).
--   $$
--
--   If moreover, for each $t\in[T]$, $f_t$ is a one-to-one map of $S_t\setminus S^*$ onto $S^*\setminus S_t$, then
--
--   $$
--   R(T)=\sum_{t=1}^T\sum_{k=1}^K\mathbf 1_{\{i_{t,k}\notin S^*\}}\big(\mu(f_t(i_{t,k}))-\mu(i_{t,k})\big).
--   $$
--
--   Such maps exist because $|S_t|=|S^*|=K$. The identity pairs each suboptimal selection with a product of $S^*$ that was missed.
--
--   **Formalization Note** Each $f_t$ is a total function, pinned by the hypothesis on $S_t\setminus S^*$; its other values do not enter the sum.
--
--   Differences from the source:
--   - encoding: f_t : S_t \ S* → S* \ S_t one-to-one and onto those sets → a total function f t with Set.BijOn on those sets; reason: the values outside S_t \ S* do not enter the sum
--   - generalization: S* the optimal set → S* any set of K products; reason: the identity does not use optimality; the optimal set is such a set
--   - generalization: α as printed → any real α; reason: the identity holds for every run
--   - reading: d, K, N, T unconstrained on the page → K ≤ N, with d, K and the period index otherwise free; reason: "selects a set of K products from [N]" (p.9) needs K ≤ N, which makes the K selections of a period distinct; the deterministic step uses no other bound
-- source:
--   Jin, Simchi-Levi, Wang, Wang, Yang, Shrinking the Upper Confidence Bound: A Dynamic Product Selection Problem for Urban Warehouses, arXiv:1903.07844v2, Start of the proof of Theorem 3, p.18

import Definitions.Def_ShrinkingUCB_regret

namespace ShrinkingUCB

/-- The start of the proof of Theorem 3, p.18 of arXiv:1903.07844v2: the regret of period `t` is
`∑_{S* \ S_t} µ − ∑_{S_t \ S*} µ`; and for any one-to-one maps `f_t` of `S_t \ S*` onto
`S* \ S_t`,
`R(T) = ∑_{t=1}^T ∑_{k=1}^K 1{i_{t,k} ∉ S*} (µ(f_t(i_{t,k})) − µ(i_{t,k}))`.

**Formalization Note.** `f t` is a total function, pinned on `S_t \ S*` by the hypothesis; its
values elsewhere do not enter the sum. -/
theorem regret_decomposition {d N : ℕ} (K T : ℕ) (hKN : K ≤ N) (I : LinearSemiBandit d N)
    (tb : TieBreak N) (α : ℝ) (o : OutcomeTable N)
    (Sstar : Finset (Fin N)) (hS : Sstar.card = K)
    (f : ℕ → Fin N → Fin N)
    (hf : ∀ t ∈ Finset.Icc 1 T,
      Set.BijOn (f t) (↑(offered I tb α K o t \ Sstar)) (↑(Sstar \ offered I tb α K o t))) :
    (∀ t ∈ Finset.Icc 1 T,
      ∑ i ∈ Sstar, I.μ i - ∑ i ∈ offered I tb α K o t, I.μ i =
        ∑ i ∈ Sstar \ offered I tb α K o t, I.μ i
          - ∑ i ∈ offered I tb α K o t \ Sstar, I.μ i) ∧
    regret I tb α K Sstar T o =
      ∑ t ∈ Finset.Icc 1 T, ∑ k ∈ Finset.Icc 1 K,
        if pick I tb α K o t k ∉ Sstar then
          I.μ (f t (pick I tb α K o t k)) - I.μ (pick I tb α K o t k)
        else 0 := by sorry

end ShrinkingUCB
