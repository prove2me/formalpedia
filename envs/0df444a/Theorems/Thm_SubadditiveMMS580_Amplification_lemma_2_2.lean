-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_lemma_2_2
-- name    : SubadditiveMMS580.Amplification.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T19:54:22.359069+00:00
-- url     : https://prove2.me/theorems/2072a7ea-7a50-470e-9793-d60074c7e584
-- title:
--   Lemma 2.2 — allocating one good and removing its recipient does not lower any other agent's MMS
-- statement:
--   Let $n\ge2$ agents have valuations $v_1,\dots,v_n:2^M\to\mathbb R$ on a finite set of goods $M$ that are normalized ($v_j(\varnothing)=0$) and monotone ($S\subseteq T\Rightarrow v_j(S)\le v_j(T)$). For a positive integer $k$ and $T\subseteq M$ let
--   $$\operatorname{MMS}_k(v;T)=\max_{(P_1,\dots,P_k)}\ \min_{j\in[k]} v(P_j),$$
--   the maximum over all ordered partitions of $T$ into $k$ possibly empty bundles, and let $\mu_j=\operatorname{MMS}_n(v_j;M)$.
--
--   Fix an agent $i$ and a good $g\in M$, and consider allocating $g$ to $i$ and removing both. Then for every agent $j\ne i$
--   $$\operatorname{MMS}_{n-1}(v_j;M\setminus\{g\})\ \ge\ \mu_j .$$
--   In particular, for every $\alpha$, if $v_i(\{g\})\ge\alpha\mu_i$ then agent $i$, who receives the bundle $\{g\}$, meets her $\alpha$-MMS target.
--
--   This is the singleton reduction: a sufficiently valuable single good can be handed out without decreasing any remaining agent's benchmark, so the main construction may assume that all singletons are worth less than the target.
--
--   **Formalization Note** Goods are `Fin m` and agents `Fin n`; the reduced instance keeps the original indexing and the statement only concerns the agents $j\ne i$. $\operatorname{MMS}$ is the published `LittleCharity.MMS.mms`, a maximum over all labellings of the goods by $[k]$ (each labelling is an ordered partition into $k$ possibly empty bundles); for $k\ge1$ the index sets are finite and nonempty, so the maximum and minimum are attained. Here $k=n$ and $k=n-1\ge1$.
--
--   Differences from the source:
--   - reading: "In particular, if $v_i(\{g\})\ge\alpha\mu_i$, this allocation meets agent $i$'s $\alpha$-MMS target" → for every real $\alpha$, $\alpha\mu_i\le v_i(\{g\})$ implies $\alpha\mu_i\le v_i(\{g\})$, the value of agent $i$'s bundle $\{g\}$; reason: the clause is kept verbatim; agent $i$'s bundle in this allocation is $\{g\}$, so meeting the target is exactly the displayed inequality.
--   - encoding: $M$ a finite set, agents $[n]$ → `Fin m`, `Fin n`; reason: relabelling; every finite instance is covered.
--   - encoding: valuations $v:2^M\to\mathbb R_{\ge0}$ → real-valued set functions with `IsNormalized` and `IsMonotone`; reason: normalization and monotonicity give $v(S)\ge v(\varnothing)=0$, so exactly the same valuations.
-- source:
--   Bo Li, Ankang Sun, STOC 2027 submission #580 (October 2026), Lemma 2.2, p. 10 (standing assumptions §2.1, p. 8)

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Setting
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_LittleCharity_MMS_Setting

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification

/-- Lemma 2.2 (Li–Sun, STOC 2027 submission #580, p. 10): for `n ≥ 2` agents with normalized
monotone valuations on the goods `Fin m`, allocating a good `g` to an agent `i` and removing both
leaves every other agent `j` with `MMS_{n-1}(v_j; M \ {g}) ≥ μ_j = MMS_n(v_j; M)`; and if
`v_i({g}) ≥ α μ_i`, the bundle `{g}` meets agent `i`'s `α`-MMS target. -/
theorem lemma_2_2 (n : ℕ) (hn : 2 ≤ n) {m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (i : Fin n) (g : Fin m) :
    (∀ j : Fin n, j ≠ i →
      LittleCharity.MMS.mms (v j) n Finset.univ ≤
        LittleCharity.MMS.mms (v j) (n - 1) (Finset.univ.erase g)) ∧
    ∀ α : ℝ, α * LittleCharity.MMS.mms (v i) n Finset.univ ≤ v i {g} →
      α * LittleCharity.MMS.mms (v i) n Finset.univ ≤ v i ({g} : Finset (Fin m)) := by sorry

end SubadditiveMMS580.Amplification
