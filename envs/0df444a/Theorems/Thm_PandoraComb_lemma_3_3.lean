-- Prove2me | Theorems.Thm_PandoraComb_lemma_3_3
-- name    : PandoraComb.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:09:35.800351+00:00
-- url     : https://prove2.me/theorems/ff73a3dc-4530-46d5-b8d2-044330440140
-- title:
--   Lemma 3.3 — $u_N(\pi)\le u_N(\pi_A\mid B)+u_N(\pi_B)$ for every partition $\pi=A\uplus B$
-- statement:
--   Let $\mathcal I$ be a Bernoulli instance with weights $v_i$, probabilities $p_i\in[0,1]$, and a cost $c$ that is normalized, monotone and submodular. Let $R$ be a set of boxes (the first box $\{r\}$ of §3.1), let $\pi=(i_1,\dots,i_k)$ be an impulsive strategy whose boxes are distinct and not in $R$, and let $A,B$ partition the boxes of $\pi$. Then
--
--   $$u_N(\pi)\ \le\ u_N(\pi_A\mid B)+u_N(\pi_B),$$
--
--   where, for $P\subseteq\pi$ and a set $T$ of boxes already opened,
--   $$u_N(\pi_P\mid T)=\sum_{j:\ i_j\in P}\prod_{l<j}(1-p_{i_l})\Big(p_{i_j}v_{i_j}-c\big(i_j\ \big|\ R\cup T\cup\{i_l:\ l<j,\ i_l\in P\}\big)\Big)$$
--   and $u_N(\pi)=u_N(\pi_\pi\mid\emptyset)$.
--
--   Splitting an impulsive strategy into two strategies with dummies, the second one charged as if the boxes of the first had been opened, never loses marginal utility. This is the main technical tool of the proof of Lemma 3.1.
--
--   Differences from the source:
--   - generalization: the conditioning set {r} ∪ T with the first box r of §3.1 → an arbitrary base set R disjoint from π; reason: the proof omits the {r} terms "This has no effect on the proof" (p.12); R = {r} is an instance
--   - generalization: weights v_i > 0 and probabilities p_i ∈ (0, 1] of §3.1, boxes in [n] → any real weights v i, probabilities p i ∈ [0, 1], boxes in any type ι with decidable equality; reason: the value terms cancel exactly (p.12), so no sign of v is used; the cost inequality is linear in each p_i, so it extends to p_i = 0; the §3.1 instance is an instance
--   - encoding: u_N(π), u_N(π_A | B), u_N(π_B) as expected marginal utilities (Definition 3.1, p.10) → the closed form uND v p c R l P T; reason: the paper's own formulas: Observation 3 (p.10) and the dummies example (p.11)
-- source:
--   Berger, Ezra, Feldman & Fusco, Pandora’s Problem with Combinatorial Cost, arXiv:2303.01078v1, Lemma 3.3, p.12 (proof pp.12–14; notation: Definition 3.1 and Observation 3, p.10; dummies, p.11)

import Definitions.Def_PandoraComb_ClosedForms
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular

namespace PandoraComb

/-- **Lemma 3.3** (arXiv:2303.01078v1, p.12): "Let π ⊆ [n] be any impulsive strategy, and let
π = A ⊍ B be a partition of the set of boxes corresponding to π. Then we have
u_N(π) ≤ u_N(π_A | B) + u_N(π_B)."

**Formalization Note.** The Bernoulli instance has values `v` and probabilities `p ∈ [0, 1]`; the
cost is normalized, monotone and submodular (§2, p.7 and §3.1, p.9). The impulsive strategy is the
tuple `l` without repetition, and `u_N(π_P | T) = uND v p c R l P T` (Definition 3.1 and
Observation 3, p.10; dummies, p.11), so `u_N(π) = uND … l l.toFinset ∅`,
`u_N(π_A | B) = uND … l A B` and `u_N(π_B) = uND … l B ∅`. The box `r` of §3.1 is a base set `R`
disjoint from `π`, present in every conditional cost term. -/
theorem lemma_3_3 {ι : Type*} [DecidableEq ι] (v p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (c : Finset ι → ℝ) (hc0 : c ∅ = 0) (hmono : Monotone c)
    (hsub : SubsamplingSM.Offline.IsSubmodular c) (R : Finset ι) (l : List ι) (hl : l.Nodup)
    (A B : Finset ι) (hAB : Disjoint A B) (hcover : A ∪ B = l.toFinset)
    (hR : Disjoint R l.toFinset) :
    uND v p c R l l.toFinset ∅ ≤ uND v p c R l A B + uND v p c R l B ∅ := by sorry

end PandoraComb
