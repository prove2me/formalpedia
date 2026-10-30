-- Prove2me | Theorems.Thm_SubsamplingSM_Offline_theorem1_union_opt_bound
-- name    : SubsamplingSM.Offline.theorem1_union_opt_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:00:33.013537+00:00
-- url     : https://prove2.me/theorems/23a608cc-35f3-4db8-8778-4c91bf8e6c0f
-- title:
--   Proof of Theorem 1, §4.1.1 — $\mathbb E[f(S\cup \mathrm{OPT})]\ge(1-\tfrac1{p+1})f(\mathrm{OPT})$
-- statement:
--   Let $p\ge1$ and $f$ non-negative and submodular, and let Algorithm 2 accept each considered element independently with probability $q=\frac1{p+1}$. Then its final solution $S$ satisfies
--   $$\mathbb E[f(S\cup O_0)]\ \ge\ \Big(1-\frac1{p+1}\Big)f(O_0),$$
--   for every starting set $O_0$, every collection $\mathcal I$ and every selection rule for $O_u$.
--
--   In the paper this is the step "each element appears in $S$ with probability at most $q$, and hence, by Lemma 3", with $O_0=\mathrm{OPT}$; it is the non-monotone input to the ratio $(p+1)^2/p$.
--
--   Differences from the source:
--   - encoding: E[·] over the independent random choices of Algorithm 2 → expectSample q over the coin vector b (Σ_b q^|b| (1−q)^(n−|b|) ·); reason: paper.md Reading 1: the coins are independent Bernoulli(q) bits fixed before the run (p. 10); same instances
--   - reading: S: the final value of Algorithm 2 (p. 12) → (alg2Run …).S after n iterations; reason: paper.md Reading 6
--   - generalization: OPT, an optimal solution, in Algorithm 2 and in f(OPT) → any set O₀, with no hypothesis; reason: paper.md generalization 7; the step uses only that S is a subset of the accepted coins
--   - generalization: (N, I) p-extendible; O_u the smallest set of Line 6 (standing assumptions) → no hypothesis on I or on the selection rule; reason: the step does not use them
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, proof of Theorem 1, §4.1.1 (unnumbered), p. 15

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_SubsamplingSM_Offline_expectSample
import Definitions.Def_SubsamplingSM_Offline_alg2Run

namespace SubsamplingSM.Offline

/-- **Lower bound on `E[f(S ∪ OPT)]` in the proof of Theorem 1.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, proof of Theorem 1, §4.1.1, p. 15 (unnumbered): "Note that each element appears in `S` with
probability at most `q = 1/(p+1)`, and hence, by Lemma 3, we have that
`E[f(S ∪ OPT)] ≥ (1 − 1/(p+1)) f(OPT)`."

Let `p ≥ 1` and `f` non-negative and submodular, and let the coins of Algorithm 2 be drawn with
`q = 1/(p+1)`. Then the final solution `S` satisfies
`E[f(S ∪ O₀)] ≥ (1 − 1/(p+1)) · f(O₀)`, for every family `I`, selection rule `sel` and set
`O₀`.

**Formalization Note.** Expectations are `expectSample q` (paper.md Reading 1) and `S` is the
final value (Reading 6). That each element is in `S` with probability at most `q` is the step
of the proof, not a hypothesis. `O₀` replaces OPT (generalization 7); the hypotheses on `I`,
`sel` and `O₀` are dropped (the step does not use them). -/
theorem theorem1_union_opt_bound {α : Type*} [Fintype α] [LinearOrder α]
    (p : ℕ) (hp : 1 ≤ p) (f : Finset α → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : IsSubmodular f)
    (I : Finset α → Prop) (sel : Finset α → Finset α → Finset α) (O₀ : Finset α) :
    (1 - 1 / ((p : ℝ) + 1)) * f O₀ ≤
      expectSample (1 / ((p : ℝ) + 1)) (fun b => f ((alg2Run f I sel O₀ b).S ∪ O₀)) := by sorry

end SubsamplingSM.Offline
