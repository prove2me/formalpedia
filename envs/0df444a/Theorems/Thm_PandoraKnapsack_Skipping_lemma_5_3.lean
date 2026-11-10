-- Prove2me | Theorems.Thm_PandoraKnapsack_Skipping_lemma_5_3
-- name    : PandoraKnapsack.Skipping.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:25:29.871084+00:00
-- url     : https://prove2.me/theorems/ed19abf6-11ba-49b3-804c-0819f700735f
-- title:
--   Lemma 5.3 — each assigned start time is reached in time with probability at least one half
-- statement:
--   Let $I$ be a valid MPK instance on the grid $\{0,\dots,T+1\}$ with capacity $T$, and let $x^*$ be an optimal solution of $\Psi(T)$. Run Algorithm 1 with $x^*$. For every item $i$, choice $j$ and time $t\in\{0,\dots,T\}$ (including $t=0$), let $s(I_{i,j})$ be the total realized size of the item-choices inserted by Algorithm 1 before $(i,j)$ in the sorted order. Then
--   $$\Pr\big[b_{i,j}=t\ \wedge\ s(I_{i,j})\le t\big]\ \ge\ \tfrac12\,\Pr\big[b_{i,j}=t\big],$$
--   that is, $\Pr(s(I_{i,j})\le t\mid b_{i,j}=t)\ge\frac12$ whenever the conditioning event has positive probability.
--
--   Differences from the source:
--   - encoding: Pr(s(I_{i,j}) ≤ t | b_{i,j} = t) ≥ 1/2 → (1/2)·Pr[b_{i,j} = t] ≤ Pr[b_{i,j} = t ∧ s(I_{i,j}) ≤ t]; reason: the two are equal when Pr[b_{i,j} = t] > 0; the joint form puts no condition on a null event
--   - encoding: Bernoulli(α_i/4) keep step followed by a Categorical(x*_{i,j,t}/α_i) draw, and sizes s_i^j → one assignment law per item (pair (j,t) with probability x*_{i,j,t}/4, none with probability 1 − α_i/4) and one size per item drawn from its assigned choice's law, on a finite product space; reason: same joint law of assignments and observed sizes; the categorical law is not evaluated when α_i = 0
--   - encoding: ties broken by increasing (i, j) → ties broken by increasing item i; reason: each item is retained with at most one choice, so the two orders coincide
--   - encoding: items [n] and choices [m] indexed from 1 → Fin n and Fin m, indexed from 0; reason: index shift; same instances
--   - reading: item-choice costs p_i^j paid up front (sign not stated) → 0 ≤ p_i^j in IsValid; reason: §2 calls p_i^j a cost incurred up front and Definition 2.1 divides by it; a negative cost would reward overflow, which the model never does
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen (2026), Pandora's Knapsack via Simple Policies, supplied PDF (STOC 2027 submission), SHA256 45e5830b173d687c08d5175988af81bf660c693ff805b1d2e7bc213140d27a2d, Lemma 5.3, printed p. 23 (PDF 25)

import Definitions.Def_PandoraKnapsack_Skipping_Algorithm1

namespace PandoraKnapsack.Skipping

/-- **Lemma 5.3** (Barak et al. 2026, *Pandora's Knapsack via Simple Policies*, supplied PDF,
SHA256 45e5830b…7a2d, printed p. 23, PDF 25). For any `i, j` and `t ∈ {0, …, T}`, with
`s(I_{i,j})` the total size of the item-choices inserted by Algorithm 1 before `(i, j)` in the
sorted order, `Pr(s(I_{i,j}) ≤ t | b_{i,j} = t) ≥ 1/2`, where `x*` is an optimal solution of
`Ψ(T)`.

**Formalization Note.** The conditional probability is written through joint probabilities,
`Pr[b_{i,j} = t ∧ s(I_{i,j}) ≤ t] ≥ ½ · Pr[b_{i,j} = t]`, which is the source's inequality when
`Pr[b_{i,j} = t] > 0` and imposes nothing on a null event. `t = 0` is included. -/
theorem lemma_5_3 {n m T : ℕ} (I : Instance n m T) (hI : IsValid I) (xStar : LPArray n m)
    (hx : PsiOptimal I T xStar) (i : Fin n) (j : Fin m) (t : Fin (T + 1)) :
    (1 / 2 : ℝ) * alg1Prob I xStar (fun ω => ω.1 i = some (j, t)) ≤
      alg1Prob I xStar (fun ω => ω.1 i = some (j, t) ∧ predecessorLoad ω i ≤ (t : ℕ)) := by sorry

end PandoraKnapsack.Skipping
