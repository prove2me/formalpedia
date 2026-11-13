-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_lemma_3_2
-- name    : SubadditiveMMS580.Amplification.lemma_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T19:54:18.667187+00:00
-- url     : https://prove2.me/theorems/a6228e86-57b6-49a4-be5d-ffe537dedde2
-- title:
--   Lemma 3.2 (Seddighin–Seddighin) — half-value partial allocation for a specified subset of agents
-- statement:
--   Let $t$ agents have valuations $v_1,\dots,v_t:2^M\to\mathbb R$ on a finite ground set $M$ that are normalized, monotone and subadditive ($v_i(S\cup T)\le v_i(S)+v_i(T)$ for all $S,T\subseteq M$), and suppose
--   $$\operatorname{MMS}_t(v_i;M)=1\qquad\text{for every agent } i,$$
--   where $\operatorname{MMS}_t$ is the maximin share over ordered partitions of $M$ into $t$ possibly empty bundles. Let $Q$ be any nonempty set of agents and $k=\lfloor t/|Q|\rfloor$. Then there is a feasible partial allocation $(A_i)$ (pairwise disjoint bundles, goods may stay unassigned) such that
--   $$\bigl|\{\,i\in Q:\ v_i(A_i)\ge \tfrac12\,\}\bigr|\ \ge\ \frac{k\,|Q|}{k+1}.$$
--
--   The lemma is the tool used to build the first three allocation layers of the layer construction (through Corollary 3.3): the specified subset $Q$ is the set of agents still to be served.
--
--   **Formalization Note** Goods are `Fin m`, agents `Fin t`. The bound compares an integer count with the real number $k|Q|/(k+1)$, computed after casting, so it is equivalent to requiring at least $\lceil k|Q|/(k+1)\rceil$ successful agents. $k=\lfloor t/|Q|\rfloor$ is natural-number division. A nonempty $Q$ forces $t\ge1$.
--
--   Differences from the source:
--   - encoding: ground set $M$, agents $1,\dots,t$ → `Fin m`, `Fin t`; reason: relabelling; every finite instance is covered.
--   - encoding: valuations $v:2^M\to\mathbb R_{\ge0}$ → real-valued set functions with `IsNormalized` and `IsMonotone`; reason: normalization and monotonicity give $v(S)\ge v(\varnothing)=0$, so exactly the same valuations.
-- source:
--   Bo Li, Ankang Sun, STOC 2027 submission #580 (October 2026), Lemma 3.2 (attributed to Seddighin–Seddighin [SS25]), p. 16

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Setting
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_LittleCharity_MMS_Setting

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification

/-- Lemma 3.2 (Seddighin–Seddighin; Li–Sun, STOC 2027 submission #580, p. 16): `t` agents with
normalized monotone subadditive valuations on `Fin m` and `MMS_t(v_i; M) = 1` for every agent.
For every nonempty set `Q` of agents, with `k = ⌊t/|Q|⌋`, some feasible partial allocation gives
value at least `1/2` to at least `k|Q|/(k+1)` agents of `Q`. -/
theorem lemma_3_2 (t : ℕ) {m : ℕ} (v : Fin t → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hsub : ∀ i, SubmodOrder.Subadditive (v i))
    (hmms : ∀ i, LittleCharity.MMS.mms (v i) t Finset.univ = 1)
    (Q : Finset (Fin t)) (hQ : Q.Nonempty) :
    ∃ A : Fin t → Finset (Fin m), IsAllocation A ∧
      ((t / Q.card : ℕ) : ℝ) * (Q.card : ℝ) / (((t / Q.card : ℕ) : ℝ) + 1) ≤
        ((Q.filter (fun i => (1 : ℝ) / 2 ≤ v i (A i))).card : ℝ) := by sorry

end SubadditiveMMS580.Amplification
