-- Prove2me | Theorems.Thm_StableMSR_Recovery_interaction_balanced_separators
-- name    : StableMSR.Recovery.interaction_balanced_separators
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T15:15:50.123492+00:00
-- url     : https://prove2.me/theorems/b8e2a18a-0fa1-4d65-bae1-438c3e682524
-- title:
--   Lemma 4.4 structural input: hereditary balanced separators within the width budget
-- statement:
--   Consider a $\gamma$-stable MSR instance with $1<\gamma<2$ and $1\le k<n$, and put $\varepsilon=\gamma-1$. Let $R$ be the largest optimal radius, $\rho=\varepsilon M/4$ the canonical density scale, and $\omega_\varepsilon=\lceil49c_\varepsilon^2+30c_\varepsilon\rceil$, where $c_\varepsilon=1+80/\varepsilon+80/\varepsilon^2$. Let $N\subseteq W$ be strictly $2R$-separated and let $\operatorname{diam}(W)\le\rho$. The interaction graph on $N$ joins distinct points at metric distance at most $8R$.
--
--   There is one integer $a\ge0$, with $15a\le\omega_\varepsilon$, such that every vertex set $U\subseteq N$ has a partition into three pairwise disjoint parts $L,S,T$ satisfying
--   $$U=L\cup S\cup T,\qquad |S|\le a,\qquad 3|L|\le2|U|,\quad3|T|\le2|U|,$$
--   and there is no interaction edge between $L$ and $T$.
--
--   This proves the hereditary balanced-separator conclusion in the linear-growth argument underlying Lemma 4.4. It includes empty vertex sets and disconnected induced subgraphs. Alignment of $W$ and maximality of $N$ are unnecessary for this structural conclusion. The statement does not assert the remaining separator-to-treewidth theorem or an executable decomposition algorithm.
--
--   **Formalization Note.** The formal statement explicitly gives the partition, absence of crossing edges, and natural-number cardinality inequalities. Balance is measured on the exclusive sides $L,T$, as in the proofs of Campbell et al., Lemmas 4–6. All clustering parameters use the existing canonical definitions; no new definition is required to state the theorem.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547v1, https://arxiv.org/html/2611.03547v1, Section 4.3, Lemma 4.4 and Theorem 4.3; Table 2. Campbell, Distel, Gollin, Harvey, Hendrey, Hickingbotham, Mohar and Wood, Graphs of Linear Growth have Bounded Treewidth, Electronic Journal of Combinatorics 30(3) (2023), P3.1, DOI 10.37236/11657, https://www.combinatorics.org/ojs/index.php/eljc/article/download/v30i3p1/pdf/, Section 2, Lemmas 4–6 and the numerical part of the proof of Theorem 1 (pp. 3–5). This theorem proves the separator consequence; Dvorak–Norin's Theorem 3 is not assumed or claimed.

import Definitions.Def_StableMSR_Recovery_Geometry
import Definitions.Def_StableMSR_Recovery_Parameters

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

theorem interaction_balanced_separators {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ ∧ γ < 2) (hkn : k < n)
    (O : Partition n) (hO : Stable d k γ O)
    (W N : Cluster n) (hNW : N ⊆ W)
    (hdiam : diameter d W ≤ densityScale d O (γ - 1))
    (hsep : ∀ x ∈ N, ∀ y ∈ N, x ≠ y → 2 * largestRadius d O < d x y) :
    ∃ a : ℕ, 15 * a ≤ widthBound (γ - 1) ∧
      ∀ U : Finset N, ∃ L S T : Finset N,
        (Disjoint L S ∧ Disjoint L T ∧ Disjoint S T ∧ L ∪ S ∪ T = U) ∧
        (∀ x ∈ L, ∀ y ∈ T, ¬ (thresholdGraph d (8 * largestRadius d O) N).Adj x y) ∧
        S.card ≤ a ∧ 3 * L.card ≤ 2 * U.card ∧ 3 * T.card ≤ 2 * U.card := by sorry

end StableMSR.Recovery
