-- Prove2me | Theorems.Thm_WeightedCoordGames_lemma_11
-- name    : WeightedCoordGames.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:54.14999+00:00
-- url     : https://prove2.me/theorems/53039cc4-5038-42e9-aa8f-c044db8377e5
-- title:
--   Lemma 11 — once a cycle below the current index has grade U+, it keeps grade U+ and the index stays above it
-- statement:
--   Consider a coordination game on an open chain $\mathcal C_1,\dots,\mathcal C_m$ with non-empty colour sets and a run $s_0\Rightarrow s_1\Rightarrow\dots\Rightarrow s_T$ of Algorithm 1, where each $\Rightarrow$ is one round of the algorithm (lines 3–8, p.17). Suppose that at some time $t\le T$ the cycle $\mathcal C_i$ has grade $\mathrm U{+}$ and
--   $$
--   \mathrm{NBR}(s_t)>i.
--   $$
--   Then for every later time $t'$ with $t\le t'\le T$, the grade of $\mathcal C_i$ given $s_{t'}$ is $\mathrm U{+}$, and $\mathrm{NBR}(s_{t'})>i$ whenever $s_{t'}$ is not a Nash equilibrium.
--
--   In words: once a cycle below the cycle being repaired has grade $\mathrm U{+}$, the algorithm never goes back to it. This gives the first component $\mathrm{guard}$ of the progress measure its monotonicity.
--
--   **Formalization Note** Cycles are 0-based in Lean, so the paper's $j>i$ becomes `i + 1 < nbr`.
--
--   Differences from the source:
--   - reading: "after line 4 of Algorithm 1 … from that moment on" → a run of rounds $s_t\Rightarrow s_{t+1}$ of Algorithm 1, the hypothesis at time $t$ and the conclusion at every later time of the run; reason: this is the execution the lemma speaks about; "$j>i$ remains true" is required only where line 4 is executed again, i.e. where $s_{t'}$ is not a Nash equilibrium
--   - reading: line 6, "the improvement path constructed in the proof of Theorem 3 or 7" → any run of the schedules of those proofs, with every choice of best responses they leave open; reason: the constructions are nondeterministic, and the lemma is claimed for whatever path line 6 produces
--   - encoding: cycles $\mathcal C_1,\dots,\mathcal C_m$ → `Fin m`, with $\mathrm{NBR}$ kept 1-based; reason: same instances
-- source:
--   Apt–Simon–Wojtczak, Coordination Games on Weighted Directed Graphs, arXiv:1910.02693v2 (preprint), §5, Lemma 11, p.17 (Algorithm 1, p.17)

import Mathlib
import Definitions.Def_WeightedCoordGames_Model
import Definitions.Def_WeightedCoordGames_Algorithm

namespace WeightedCoordGames

/-- **Lemma 11** (Apt–Simon–Wojtczak, arXiv:1910.02693v2, §5, p.17). Suppose that after line 4
of Algorithm 1 the grade of a cycle `C_i` given `s` is `U+` and `j > i`. Then from that moment on
`j > i` remains true and the grade of `C_i` remains `U+`.

Run form: let `s_0, s_1, …, s_T` be successive joint strategies of Algorithm 1
(`AlgStep s_t s_{t+1}` for `t < T`). If at time `t ≤ T` the grade of `C_i` is `U+` and
`NBR(s_t) > i`, then at every later time `t' ≤ T` the grade of `C_i` is `U+`, and
`NBR(s_{t'}) > i` whenever `s_{t'}` is not a Nash equilibrium (i.e. whenever line 4 is executed
again).

**Formalization Note.** Cycles are 0-based (`i : Fin m` is the paper's `C_{i+1}`) while `NBR` is
1-based, so the paper's `j > i` reads `i + 1 < NBR`. -/
theorem lemma_11 {V M : Type*} [Fintype V] [DecidableEq V] [Fintype M] [DecidableEq M]
    {m v : ℕ} (O : OpenChain V m v) (C : V → Finset M) (hC : ∀ u, (C u).Nonempty)
    (T : ℕ) (σ : ℕ → V → M) (hrun : ∀ t < T, O.AlgStep C (σ t) (σ (t + 1)))
    (t : ℕ) (ht : t ≤ T) (i : Fin m)
    (hU : O.grade C (σ t) i = .Uplus) (hj : i.val + 1 < O.nbr C (σ t)) :
    ∀ t', t ≤ t' → t' ≤ T →
      O.grade C (σ t') i = .Uplus ∧
        (¬ (chainGame O C).toGame.IsNash (σ t') → i.val + 1 < O.nbr C (σ t')) := by sorry

end WeightedCoordGames
