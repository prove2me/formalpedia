-- Prove2me | Theorems.Thm_PrivPCP_corollary_4_4
-- name    : PrivPCP.corollary_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:46:51.754865+00:00
-- url     : https://prove2.me/theorems/e361d6d1-515b-4417-a4f8-5568f3eb558b
-- title:
--   Corollary 4.4: relative robust testability of punctured tensor Reed–Solomon codes
-- statement:
--   There is an absolute constant $C_0>0$ such that the following holds. Under the hypotheses of Corollary 4.3 (prime $q$, $k\ge2$, $\eta\in(0,1)$, $\beta\ge1$, subgroups $S_i\le\mathbb F_q^\times$ of pairwise coprime and $\beta$-balanced orders, $H_i$ with $h_i\ge1$ and $H_i\cap S_i=\emptyset$, $a_i-h_i\ge\eta s_i$, $a_i+1<s_i$, and product expansion with constant $\rho\in(0,1]$ at every arity $2\le r\le k$), every $M\in\mathbb F_q^\Omega$ satisfies
--   $$\mathrm{dist}(M,K^\perp)\le C(\rho,k)\sum_{i=1}^k\mathrm{dist}(M,D_i),\qquad C(\rho,k)=\exp\!\big(C_0(k^3+k^2\log(1/\rho))\big).$$
--
--   This is Corollary 4.10 for the punctured Reed–Solomon codes of §4.1, and the constant $C(\rho,k)$ of the privacy bound of the main result.
--
--   Differences from the source:
--   - reading: $C(\rho,k)=\exp(O(k^3+k^2\log(1/\rho)))$ → $\exp(C_0(k^3+k^2\log(1/\rho)))$ with one absolute $C_0$ fixed before $q,k,\eta,\beta,\rho$ and the codes; reason: the standard meaning of $O(\cdot)$
--   - generalization: Conjecture 4.2 assumed for $k>2$, $\rho=\rho(k,\eta,\beta)$ → any $\rho\in(0,1]$ with $\mathrm{PunctRSPE}(r,\eta,\beta,\rho)$ for every $2\le r\le k$; reason: as in Corollary 4.3; the paper's $\rho(k,\eta,\beta)$ satisfies it
--   - encoding: §4.1's $h_i\le a_i<s_i$ → not stated separately; reason: implied by $a_i-h_i\ge\eta s_i>0$ and $a_i+1<s_i$
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Corollary 4.4, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_PrivPCP_PunctRSPE
import Definitions.Def_PrivPCP_rsNested

namespace PrivPCP

/-- **Corollary 4.4 (RS relative robust testability)** (Bafna, Vyas, *Private PCPs from Product Expansion*,
STOC 2027 submission manuscript (sha256 c2cac1e0…), Corollary 4.4, p.14). There is an absolute constant `C₀`
such that, under the hypotheses of Corollary 4.3 (prime `q`, `k ⩾ 2`, subgroups `S_i ⩽ 𝔽_q^×` of pairwise
coprime, `β`-balanced orders, `H_i` with `h_i ⩾ 1`, `H_i ∩ S_i = ∅`, `a_i − h_i ⩾ η s_i`, `a_i + 1 < s_i`, and
product expansion with constant `ρ ∈ (0,1]` at every arity `2 ⩽ r ⩽ k`), every `M ∈ 𝔽_q^Ω` satisfies
`dist(M, K^⊥) ⩽ C(ρ, k) ∑_i dist(M, D_i)`, `C(ρ, k) = exp(C₀(k³ + k² log(1/ρ)))`.

**Formalization Note** "`C(ρ, k) = exp(O(k³ + k² log(1/ρ)))`" is read with one absolute `C₀`, fixed before
`q`, `k`, `η`, `β`, `ρ` and the codes. The conjecture hypothesis is read as in `corollary_4_3`. -/
theorem corollary_4_4 : ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (q : ℕ) [Fact q.Prime] (k : ℕ), 2 ≤ k → ∀ η β ρ : ℝ, 0 < η → η < 1 → 1 ≤ β → 0 < ρ → ρ ≤ 1 →
    (∀ r, 2 ≤ r → r ≤ k → PunctRSPE r η β ρ) →
    ∀ S : Fin k → Subgroup (ZMod q)ˣ,
    (∀ i j, i ≠ j → Nat.Coprime (Nat.card (S i)) (Nat.card (S j))) →
    (∀ i j, β⁻¹ ≤ (Nat.card (S i) : ℝ) / Nat.card (S j) ∧ (Nat.card (S i) : ℝ) / Nat.card (S j) ≤ β) →
    ∀ H : Fin k → Finset (ZMod q), (∀ i, 1 ≤ (H i).card ∧ Disjoint (H i) (subgroupSet (S i))) →
    ∀ a : Fin k → ℕ, (∀ i, η * Nat.card (S i) ≤ (a i : ℝ) - (H i).card ∧ a i + 1 < Nat.card (S i)) →
    ∀ M : (∀ i, ↥((subgroupSet (S i) : Finset (ZMod q)) : Set (ZMod q))) → ZMod q,
      (distTo M (rsNested (fun i => subgroupSet (S i)) H a).Dbig : ℝ) ≤
        Real.exp (C₀ * (k ^ 3 + k ^ 2 * Real.log (1 / ρ))) *
          ∑ i, (distTo M ((rsNested (fun i => subgroupSet (S i)) H a).D i) : ℝ) := by sorry

end PrivPCP
