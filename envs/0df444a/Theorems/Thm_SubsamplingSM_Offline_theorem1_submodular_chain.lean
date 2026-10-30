-- Prove2me | Theorems.Thm_SubsamplingSM_Offline_theorem1_submodular_chain
-- name    : SubsamplingSM.Offline.theorem1_submodular_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:59:38.306079+00:00
-- url     : https://prove2.me/theorems/ee048b06-d597-4a7c-a121-d311a55f03f8
-- title:
--   Proof of Theorem 1, §4.1.1 — the submodular chain $\mathbb E[f(S)]\ge\mathbb E[f(S\cup \mathrm{OPT})]-p\,\mathbb E[f(S)]$
-- statement:
--   Let $p\ge1$, $(N,\mathcal I)$ $p$-extendible, $f$ non-negative and submodular, $O_0\in\mathcal I$ the starting set of Algorithm 2, $O_u$ chosen by a minimum-removal rule, and $q=\frac1{p+1}$. Then
--   $$\begin{aligned}
--   \mathbb E[f(S)]&\ge \mathbb E[f(S\cup O_0)]-\sum_{u\in N}\mathbb E\big[|O_u\setminus S|\cdot f(u\mid S_u)\big]\\
--   &\ge \mathbb E[f(S\cup O_0)]-\frac{p}{p+1}\sum_{u\in N}\mathbb E\big[X_u\, f(u\mid S_u)\big]\\
--   &\ge \mathbb E[f(S\cup O_0)]-p\cdot\mathbb E[f(S)],
--   \end{aligned}$$
--   the three steps being Lemmas 6, 7 and 8. All three inequalities are asserted.
--
--   Combined with $\mathbb E[f(S\cup\mathrm{OPT})]\ge f(\mathrm{OPT})$ for monotone $f$, or with the bound from Lemma 3 otherwise, this yields the ratios $p+1$ and $(p+1)^2/p$.
--
--   Differences from the source:
--   - encoding: E[·] over the independent random choices of Algorithm 2 → expectSample q over the coin vector b (Σ_b q^|b| (1−q)^(n−|b|) ·); reason: paper.md Reading 1: the coins are independent Bernoulli(q) bits fixed before the run (p. 10); same instances
--   - reading: S, O_u, S_u, X_u (Y_u): the final values of Algorithm 2 (p. 12) → fields of alg2Run after n iterations; X_u = considered, Y_u = yIndicator; reason: paper.md Reading 6: the loop stops within n iterations and later iterations are the identity
--   - generalization: Algorithm 2 starts from O = OPT, an optimal solution → any starting set O₀ with O₀ ∈ I; reason: paper.md generalization 7: the proof never uses optimality; OPT ∈ I is an instance
--   - generalization: O_u is "the smallest set" of Line 6 (unspecified among ties) → O_u = sel(O, S) for any rule sel with IsMinRemoval I sel; reason: paper.md generalization 8: every choice of smallest set is such a rule
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, proof of Theorem 1, §4.1.1 (unnumbered display), p. 14

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_SubsamplingSM_Offline_IsPExtendible
import Definitions.Def_SubsamplingSM_Offline_IsMinRemoval
import Definitions.Def_SubsamplingSM_Offline_expectSample
import Definitions.Def_SubsamplingSM_Offline_considered

namespace SubsamplingSM.Offline

/-- **The chain of the proof of Theorem 1 for submodular objectives.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, proof of Theorem 1, §4.1.1, p. 14 (unnumbered display): "Note that `q = 1/(p+1)`, and
therefore,
`E[f(S)] ≥ E[f(S ∪ OPT)] − Σ_{u∈N} E[|Ou \ S| · f(u | Su)]` (Lemma 6)
`≥ E[f(S ∪ OPT)] − p/(p+1) Σ_{u∈N} E[Xu · f(u | Su)]` (Lemma 7)
`≥ E[f(S ∪ OPT)] − p · E[f(S)]` (Lemma 8)."

Let `p ≥ 1`, `I` a p-extendible system, `f` non-negative and submodular, `O₀ ∈ I` and
`sel` a minimum-removal rule, and let the coins be drawn with `q = 1/(p+1)`. The three
inequalities of the display hold, in this order; in particular
`E[f(S)] ≥ E[f(S ∪ O₀)] − p · E[f(S)]`.

**Formalization Note.** Expectations are `expectSample q` (paper.md Reading 1), `S`, `O_u`,
`S_u` are final values (Reading 6), `X_u` is `considered`; `O₀ ∈ I` replaces OPT
(generalization 7) and `sel` is any minimum-removal rule (generalization 8). -/
theorem theorem1_submodular_chain {α : Type*} [Fintype α] [LinearOrder α]
    (p : ℕ) (hp : 1 ≤ p) (I : Finset α → Prop) (hI : IsPExtendible I p)
    (f : Finset α → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : IsSubmodular f)
    (sel : Finset α → Finset α → Finset α) (hsel : IsMinRemoval I sel)
    (O₀ : Finset α) (hO₀ : I O₀) :
    (expectSample (1 / ((p : ℝ) + 1)) (fun b => f ((alg2Run f I sel O₀ b).S ∪ O₀)) -
        ∑ u : α, expectSample (1 / ((p : ℝ) + 1)) (fun b =>
          (((alg2Run f I sel O₀ b).Ou u \ (alg2Run f I sel O₀ b).S).card : ℝ) *
            marg f ((alg2Run f I sel O₀ b).Su u) u)
      ≤ expectSample (1 / ((p : ℝ) + 1)) (fun b => f (alg2Run f I sel O₀ b).S)) ∧
    (expectSample (1 / ((p : ℝ) + 1)) (fun b => f ((alg2Run f I sel O₀ b).S ∪ O₀)) -
        ((p : ℝ) / ((p : ℝ) + 1)) * ∑ u : α, expectSample (1 / ((p : ℝ) + 1)) (fun b =>
          considered f I sel O₀ b u * marg f ((alg2Run f I sel O₀ b).Su u) u)
      ≤ expectSample (1 / ((p : ℝ) + 1)) (fun b => f ((alg2Run f I sel O₀ b).S ∪ O₀)) -
        ∑ u : α, expectSample (1 / ((p : ℝ) + 1)) (fun b =>
          (((alg2Run f I sel O₀ b).Ou u \ (alg2Run f I sel O₀ b).S).card : ℝ) *
            marg f ((alg2Run f I sel O₀ b).Su u) u)) ∧
    (expectSample (1 / ((p : ℝ) + 1)) (fun b => f ((alg2Run f I sel O₀ b).S ∪ O₀)) -
        (p : ℝ) * expectSample (1 / ((p : ℝ) + 1)) (fun b => f (alg2Run f I sel O₀ b).S)
      ≤ expectSample (1 / ((p : ℝ) + 1)) (fun b => f ((alg2Run f I sel O₀ b).S ∪ O₀)) -
        ((p : ℝ) / ((p : ℝ) + 1)) * ∑ u : α, expectSample (1 / ((p : ℝ) + 1)) (fun b =>
          considered f I sel O₀ b u * marg f ((alg2Run f I sel O₀ b).Su u) u)) := by sorry

end SubsamplingSM.Offline
