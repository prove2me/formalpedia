-- Prove2me | Theorems.Thm_SupplyChainTheory_flex_supermodular
-- name    : SupplyChainTheory.flex_supermodular
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:11:13.45567+00:00
-- url     : https://prove2.me/theorems/3e47a35f-1de8-4aed-b8cd-1b8d292a672a
-- title:
--   Lemma 7.5: sales are supermodular in the flexible edges of the long chain, $P(d, E) + P(d, E \setminus \{\alpha, \beta\}) \ge P(d, E \setminus \{\alpha\}) + P(d, E \setminus \{\beta\})$
-- statement:
--   **Lemma 7.5.** Let $E \subseteq C_n$ be a flexibility design for a balanced system of size $n$
--   with plant capacity $C \ge 0$, and let $\alpha$ and $\beta$ be two flexible edges in $E$. Then
--   for every demand realization $d \ge 0$,
--
--   $$ P(d, E) + P(d, E \setminus \{\alpha, \beta\}) \;\ge\; P(d, E \setminus \{\alpha\}) + P(d, E \setminus \{\beta\}), $$
--
--   where $P(d, E)$ is the maximum sales (7.22) under design $E$. Adding the second flexible edge
--   back into $E \setminus \{\alpha, \beta\}$ brings at least as much marginal benefit as adding the
--   first. The book omits the proof and cites Simchi-Levi and Wei (2012). This is the realization-
--   level fact behind everything that follows; its expectation is Corollary 7.6.
--
--   **Formalization Note** The book's "two flexible edges" are not required to be distinct; when
--   $\alpha = \beta$ the inequality reduces to monotonicity of $P$ in $E$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 249, Sect. 7.5.3, Lemma 7.5, Eq. (7.27): 'Proof. Omitted; see Simchi-Levi and Wei (2012)'

import Definitions.Def_SupplyChainTheory_flexibility

namespace SupplyChainTheory

theorem flex_supermodular {n : ℕ} (C : ℝ) (hC : 0 ≤ C) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (E : Finset (Fin n × Fin n)) (hE : E ⊆ longChain n) (a b : Fin n × Fin n)
    (ha : a ∈ E) (hb : b ∈ E) (hfa : IsFlexEdge a) (hfb : IsFlexEdge b) :
    perf C d (E \ {a}) + perf C d (E \ {b}) ≤ perf C d E + perf C d (E \ {a, b}) := by sorry

end SupplyChainTheory
