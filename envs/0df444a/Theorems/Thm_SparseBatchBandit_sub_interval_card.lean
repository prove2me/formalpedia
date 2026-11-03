-- Prove2me | Theorems.Thm_SparseBatchBandit_sub_interval_card
-- name    : SparseBatchBandit.sub_interval_card
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:28:55.281941+00:00
-- url     : https://prove2.me/theorems/bc567e32-e710-4f98-bf67-765be9e257ad
-- title:
--   Proof of Lemma 5, p.26 — $|T_m^{(j)}|=\Omega(\sqrt{Ts_0}/M)$
-- statement:
--   Under the regime of Theorem 2 there are $c>0$ and $T_0$, depending only on $A,\varepsilon,\beta,p$, such that for $T\ge T_0$ and all $j,m\in[M]$,
--
--   $$
--   |T_m^{(j)}|\ge c\,\frac{\sqrt{Ts_0}}{M}.
--   $$
--
--   So every sub-interval of every batch contains a polynomially large number of rounds, which is what drives the concentration in Lemmas 5 and 6.
--
--   Differences from the source:
--   - reading: O, Ω and Poly with numerical constants → ∀ A ε β p, ∃ constants, ∀ instance; reason: the implied constants of the hypotheses are the only reading under which a bound can hold: a constant uniform over them would allow d = exp(T)
--   - reading: b = Θ(√T (T/s₀)^(1/(2(2^M−1)))), t₁ = b√s₀, t_m = ⌊b√t_{m−1}⌋, t_M = T → exact b, floors on every t_m, each capped at T, last point T; reason: the page leaves b open up to Θ, and a grid point is a round; this b makes the unrounded recursion end exactly at T
--   - reading: each batch is partitioned into M intervals evenly → q-th round in T_m^(j) iff ⌊(j−1)n/M⌋ < q ≤ ⌊jn/M⌋; reason: the page gives no formula; this is the even floor partition
--   - generalization: M = O(log log(T/s₀)) → M ≤ A max(1, log log(T/s₀)); reason: keeps the small instances with log log(T/s₀) ≤ 1; large instances are the paper's
--   - reading: |T_m^(j)| = Ω(√(Ts₀)/M) → c√(Ts₀)/M ≤ |T_m^(j)| for T ≥ T₀; reason: an Ω is asymptotic: at small T a sub-interval can be empty
--   - encoding: no explicit ranges → T ≥ 2, d ≥ 1, K ≥ 2, M ≥ 1, s₀ ≥ 1, γ, ρ > 0; reason: the formulas degenerate outside them: K = 1 gives log K = 0 and T = 1, d = 1 makes the right side 0
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, proof of Lemma 5, p.26

import Mathlib
import Definitions.Def_SparseBatchBandit_Regime
import Definitions.Def_SparseBatchBandit_subInterval

namespace SparseBatchBandit

/-- **Sizes of the sub-intervals**, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, proof of Lemma 5, p.26 (PDF 26):
`|T_m^{(j)}| = Ω(√(Ts₀)/M)` for any `j, m ∈ [M]`.

**Formalization Note.** The `Ω` becomes `c`. The threshold `T₀` is needed: at small `T` a
sub-interval can be empty. `c` and `T₀` depend only on `A, ε, β, p`. -/
theorem sub_interval_card (A ε β : ℝ) (p : ℕ) (_hA : 0 < A) (_hε : 0 < ε) (_hβ : 0 < β) :
    ∃ (c : ℝ) (T₀ : ℕ), 0 < c ∧
      ∀ (T d K M s₀ : ℕ) (γ ρ : ℝ), Regime A ε β p T d K M s₀ γ ρ → T₀ ≤ T →
        ∀ m ∈ Finset.Icc 1 M, ∀ j ∈ Finset.Icc 1 M,
          c * Real.sqrt ((T : ℝ) * s₀) / M ≤ ((subInterval T s₀ M m j).card : ℝ) := by sorry

end SparseBatchBandit
