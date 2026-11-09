-- Prove2me | Theorems.Thm_PrivPCP_corollary_4_3
-- name    : PrivPCP.corollary_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:46:49.320651+00:00
-- url     : https://prove2.me/theorems/51eaeca6-ffa0-4551-8807-9e1c5bdc9645
-- title:
--   Corollary 4.3: relative dual distance of punctured tensor Reed–Solomon codes
-- statement:
--   Let $q$ be prime, $k\ge2$, $\eta\in(0,1)$, $\beta\ge1$, and let $S_1,\dots,S_k\le\mathbb F_q^\times$ be subgroups of pairwise coprime orders $s_i$ with $\beta^{-1}\le s_i/s_j\le\beta$. Let $H_i\subseteq\mathbb F_q$ have $h_i=|H_i|\ge1$ and $H_i\cap S_i=\emptyset$, and let $a$ be a degree profile with
--   $$a_i-h_i\ge\eta s_i,\qquad a_i+1<s_i\qquad(i\in[k]).$$
--   Let $V_i=\mathrm{RS}(S_i,a_i+1)$, $K_i=\{\mathrm{ev}_{S_i}(p):\deg p\le a_i,\ p|_{H_i}=0\}$, and $C$, $K$ as in §4, $N=\prod_i s_i$. Let $\rho\in(0,1]$ be such that the product-expansion property of Conjecture 4.2 (rate margin $\eta$, balance $\beta$) holds with constant $\rho$ at every arity $2\le r\le k$. Then
--   $$\mathrm{wt}(M)\ge\eta\,\rho^{k-1}N\qquad(M\in K^\perp\setminus C^\perp).$$
--
--   By (2), this says that the uniform low-degree extension of a table on $D=\prod_iH_i$ hides the table from every view of fewer than $\eta\rho^{k-1}N$ coordinates.
--
--   Differences from the source:
--   - generalization: if $k>2$ assume Conjecture 4.2, and put $\rho=\rho(k,\eta,\beta)$ → any $\rho\in(0,1]$ with $\mathrm{PunctRSPE}(r,\eta,\beta,\rho)$ for every $2\le r\le k$; reason: the proof (p.14) uses exactly this; under the paper's assumptions (Conjecture 4.2 for $r>2$, Theorem 4.11 for $r=2$, $\rho(\cdot,\eta,\beta)$ nonincreasing in $r$) $\rho(k,\eta,\beta)$ satisfies it
--   - encoding: §4.1's $h_i\le a_i<s_i$ → not stated separately; reason: implied by $a_i-h_i\ge\eta s_i>0$ and $a_i+1<s_i$
--   - encoding: subgroups $S_i$ as evaluation sets → the set of their elements in $\mathbb F_q$ (`subgroupSet`); reason: same sets
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Corollary 4.3, p.14 (PDF p.16); §4.1, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_PrivPCP_PunctRSPE
import Definitions.Def_PrivPCP_rsNested

namespace PrivPCP

/-- **Corollary 4.3 (RS relative dual distance)** (Bafna, Vyas, *Private PCPs from Product Expansion*, STOC 2027
submission manuscript (sha256 c2cac1e0…), Corollary 4.3, p.14, in the set-up of §4.1, p.13). Let `q` be prime,
`k ⩾ 2`, `S_1, …, S_k ⩽ 𝔽_q^×` subgroups of pairwise coprime orders `s_i` with `β^{−1} ⩽ s_i/s_j ⩽ β`,
`H_i ⊆ 𝔽_q` with `h_i = |H_i| ⩾ 1` and `H_i ∩ S_i = ∅`, and `a` a degree profile with `a_i − h_i ⩾ η s_i` and
`a_i + 1 < s_i`. Let `V_i = RS(S_i, a_i + 1)`, `K_i = {ev_{S_i}(p) : deg p ⩽ a_i, p|_{H_i} = 0}`, and `C`, `K`
as in §4. If the product-expansion property of Conjecture 4.2 holds with constant `ρ ∈ (0,1]` at every arity
`2 ⩽ r ⩽ k`, then `wt(M) ⩾ η ρ^{k−1} N` for every `M ∈ K^⊥ ∖ C^⊥`, `N = ∏_i s_i`.

**Formalization Note** The paper assumes Conjecture 4.2 (for `k > 2`; Theorem 4.11 at arity 2) and puts
`ρ = ρ(k, η, β)`, with `ρ(·, η, β)` nonincreasing in the arity. That makes every arity `2 ⩽ r ⩽ k`
`ρ(k, η, β)`-product-expanding, which is the hypothesis `hconj` here; nothing else of the conjecture is used. -/
theorem corollary_4_3 {q : ℕ} [Fact q.Prime] {k : ℕ} (hk : 2 ≤ k) (η β ρ : ℝ) (hη : 0 < η ∧ η < 1)
    (hβ : 1 ≤ β) (hρ : 0 < ρ ∧ ρ ≤ 1) (hconj : ∀ r, 2 ≤ r → r ≤ k → PunctRSPE r η β ρ)
    (S : Fin k → Subgroup (ZMod q)ˣ)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (Nat.card (S i)) (Nat.card (S j)))
    (hbal : ∀ i j, β⁻¹ ≤ (Nat.card (S i) : ℝ) / Nat.card (S j) ∧ (Nat.card (S i) : ℝ) / Nat.card (S j) ≤ β)
    (H : Fin k → Finset (ZMod q)) (hH : ∀ i, 1 ≤ (H i).card ∧ Disjoint (H i) (subgroupSet (S i)))
    (a : Fin k → ℕ) (ha : ∀ i, η * Nat.card (S i) ≤ (a i : ℝ) - (H i).card ∧ a i + 1 < Nat.card (S i)) :
    ∀ M ∈ (rsNested (fun i => subgroupSet (S i)) H a).Dbig, M ∉ (rsNested (fun i => subgroupSet (S i)) H a).B →
      η * ρ ^ (k - 1) * (Fintype.card (∀ i, ↥((subgroupSet (S i) : Finset (ZMod q)) : Set (ZMod q))) : ℝ) ≤
        GoodQLTC.supportCard M := by sorry

end PrivPCP
