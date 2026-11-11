-- Prove2me | Theorems.Thm_PermDiameter_Binary_lemma_3_3
-- name    : PermDiameter.Binary.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:11:38.303622+00:00
-- url     : https://prove2.me/theorems/9b63c855-ea7c-480d-bf14-517481248b6c
-- title:
--   Lemma 3.3 — the length gap: $\langle\Sigma_1\rangle=G_1$, $g_1\in Z(G_1)\setminus\{1\}$, $\ell(g_0)\le k_0\Rightarrow\ell(g_1)\le k_1$, $\ell(g_0)>k_0\Rightarrow\ell(g_1)>m$
-- statement:
--   Let $(\Sigma_0,g_0,k_0)$ be an instance of Binary Length with $g_0\in G_0=\langle\Sigma_0\rangle$ and $1\in\Sigma_0$, and let $q,m,d_c,c$ be Step 1 data: $q=4m-3$, $m\ge k_0+10(d_0+d_c)^4+3$, and $c$ a permutation of order $q^2$. With $G_1=G_0\times C_{q^2}$, $\Sigma_1$, $g_1=(1,c^{q+k_0})$ and $k_1=k_0+1$ as in Step 1: the set $\Sigma_1$ generates $G_1$, $g_1\in Z(G_1)\setminus\{1\}$, and
--   $$\ell(g_0,\Sigma_0)\le k_0\implies \ell(g_1,\Sigma_1)\le k_1,\qquad \ell(g_0,\Sigma_0)>k_0\implies \ell(g_1,\Sigma_1)>m .$$
--   This turns the instance into one whose target is central and whose length is either at most $k_1$ or larger than the much bigger threshold $m$.
--
--   **Formalization Note.** `D : LengthGapData Σ₀ g₀ k₀` carries $g_0\in G_0$, $1\in\Sigma_0$ and the Step 1 data; lengths are `wordLength` in `ℕ∞`. Centrality is $g_1\in G_1$ and $g_1h=hg_1$ for all $h\in G_1$.
--
--   Differences from the source:
--   - generalization: q, m, d_c, c given by (3.1) and Lemma 3.2 → any q, m, d_c with q = 4m − 3 and (3.2), and any c of order q²; reason: the paper's choice satisfies these properties, so the statement specializes to the paper's
--   - encoding: permutations compose left to right → Mathlib's Equiv.Perm composes right to left, every formula kept as printed; reason: the statement and its proof use only the group operations, so it is the same lemma for the opposite composition convention
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), p. 13, Lemma 3.3

import Mathlib
import Definitions.Def_PermDiameter_Binary_WordLength
import Definitions.Def_PermDiameter_Binary_LengthGap

open Equiv

namespace PermDiameter.Binary

/-- **Lemma 3.3** (the length gap). `Σ₁` generates `G₁`, and `g₁ ∈ Z(G₁) ∖ {1}`. Moreover
`ℓ(g₀, Σ₀) ≤ k₀ ⟹ ℓ(g₁, Σ₁) ≤ k₁` and `ℓ(g₀, Σ₀) > k₀ ⟹ ℓ(g₁, Σ₁) > m`. -/
theorem lemma_3_3 {d0 : ℕ} {Sig0 : Finset (Perm (Fin d0))} {g0 : Perm (Fin d0)} {k0 : ℕ}
    (D : LengthGapData Sig0 g0 k0) :
    Subgroup.closure (D.Sig1 : Set (Perm (Omega1 d0 D.dc))) = D.G1 ∧
    (D.g1 ∈ D.G1 ∧ (∀ h ∈ D.G1, D.g1 * h = h * D.g1) ∧ D.g1 ≠ 1) ∧
    (wordLength (Sig0 : Set (Perm (Fin d0))) g0 ≤ (k0 : ℕ∞) →
      wordLength (D.Sig1 : Set (Perm (Omega1 d0 D.dc))) D.g1 ≤ (D.k1 : ℕ∞)) ∧
    ((k0 : ℕ∞) < wordLength (Sig0 : Set (Perm (Fin d0))) g0 →
      (D.m : ℕ∞) < wordLength (D.Sig1 : Set (Perm (Omega1 d0 D.dc))) D.g1) := by sorry

end PermDiameter.Binary
