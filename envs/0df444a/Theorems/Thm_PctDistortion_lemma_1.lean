-- Prove2me | Theorems.Thm_PctDistortion_lemma_1
-- name    : PctDistortion.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:41:59.56478+00:00
-- url     : https://prove2.me/theorems/15190968-64d7-4396-801c-f0ed517e83ac
-- title:
--   Lemma 1 — $M_\alpha$ is closed under composition and under extensions
-- statement:
--   Fix $\alpha\in[1/2,1)$. Let $\mathcal E_G=(V_G,C_G,\vec\succ_G)$ be an election whose candidates are the nodes of $G=G^\alpha_{\mathcal E_G}\in M_\alpha$, and for every node $i$ let $\mathcal E_i=(V_i,C_i,\vec\succ_i)$ be an election with $H_i=G^\alpha_{\mathcal E_i}\in M_\alpha$. Consider the composite election $\mathcal E$ with candidates $C=\biguplus_i C_i$ and voters $V=V_G\times\prod_i V_i$, in which $v=(v_G,(v_i)_i)$ ranks $c\in C_i$ ahead of $c'\in C_{i'}$ iff $v_G$ ranks $i$ ahead of $i'$ (when $i\ne i'$), or $v_i$ ranks $c$ ahead of $c'$ (when $i=i'$). Then:
--
--   1. these rankings are strict total orders, so $\mathcal E$ is an election;
--   2. the α-majority digraph of $\mathcal E$ is exactly the composition: $G^\alpha_{\mathcal E}=G[H_1,\dots,H_{|V|}]$;
--   3. in particular $G[H_1,\dots,H_{|V|}]\in M_\alpha$;
--   4. $M_\alpha$ is closed under composition;
--   5. $M_\alpha$ is closed under extensions.
--
--   Closure under extensions is what allows Theorem 3 to be applied to $M_\alpha$ in the proof of Theorem B.
--
--   Differences from the source:
--   - encoding: finite elections with n voters and m candidates → finite nonempty voter and candidate types; reason: the percentile cost and the lotteries presuppose n, m ≥ 1; with n = 0 the cost is undefined and with m = 0 there is no lottery
--   - reading: "Consider an election E … ranks the candidates as follows" → the existence of an election with these rankings (part 1), and part 2 for every election with these rankings; reason: the paper presupposes that the composite rankings are total orders
--   - encoding: C = ⊎ C_i and V = V_G × ∏ V_i → Σ i, C_i and V_G × (∀ i, V_i); reason: standard disjoint union and product types
--   - reading: "all extensions" → extensions replacing every vertex by k_i ≥ 1 independent nodes; reason: a digraph has at least one node and every member of M_α is nonempty
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 1, p.10 (proof App. G.1, p.45)

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_alphaMajority
import Definitions.Def_PctDistortion_composition
import Definitions.Def_PctDistortion_compositeRanking

set_option autoImplicit false

namespace PctDistortion

/-- **Lemma 1** (closure of `M_α` under composition). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 1, p.10 (proof App. G.1, p.45).

Fix `α ∈ [1/2, 1)`, an election `E_G` on candidates `I` (so `G = G^α_{E_G} ∈ M_α`) and elections
`E_i` on candidates `C_i` (so `H_i = G^α_{E_i} ∈ M_α`). Then:
1. there is an election on voters `V_G × ∏_i V_i` and candidates `⊎_i C_i` whose rankings are the
   composite rankings of Lemma 1 (`compositeRanking`);
2. the α-majority digraph of every such election is exactly the composition
   `G[H_1, …, H_{|V|}]`;
3. in particular `G[H_1, …, H_{|V|}] ∈ M_α`;
4. `M_α` is closed under composition;
5. `M_α` is closed under extensions.

**Formalization Note.** Part 1 records that the composite rankings are strict total orders (the
paper's "Consider an election E"). Extensions replace every vertex by `k i ≥ 1` nodes. All elections
have finite nonempty voter and candidate sets. -/
theorem lemma_1 (α : ℝ) (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 1)
    {I VG : Type} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype VG] [Nonempty VG]
    {Vi Ci : I → Type} [∀ i, Fintype (Vi i)] [∀ i, Nonempty (Vi i)] [∀ i, Fintype (Ci i)]
    [∀ i, Nonempty (Ci i)] (EG : Election VG I) (Ei : ∀ i, Election (Vi i) (Ci i)) :
    (∃ E : Election (VG × ∀ i, Vi i) (Σ i, Ci i), E.prefers = compositeRanking EG Ei) ∧
    (∀ E : Election (VG × ∀ i, Vi i) (Σ i, Ci i), E.prefers = compositeRanking EG Ei →
      alphaMajority α E = composition (alphaMajority α EG) (fun i => alphaMajority α (Ei i))) ∧
    IsAlphaMajority α (composition (alphaMajority α EG) (fun i => alphaMajority α (Ei i))) ∧
    (∀ (J : Type) (G : Digraph J) (W : J → Type) (H : ∀ j, Digraph (W j)),
      IsAlphaMajority α G → (∀ j, IsAlphaMajority α (H j)) → IsAlphaMajority α (composition G H)) ∧
    (∀ (J : Type) (G : Digraph J) (k : J → ℕ), (∀ j, 1 ≤ k j) →
      IsAlphaMajority α G → IsAlphaMajority α (extension G k)) := by sorry

end PctDistortion
