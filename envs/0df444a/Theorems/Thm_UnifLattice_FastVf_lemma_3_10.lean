-- Prove2me | Theorems.Thm_UnifLattice_FastVf_lemma_3_10
-- name    : UnifLattice.FastVf.lemma_3_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:21:07.370677+00:00
-- url     : https://prove2.me/theorems/6c36fc16-7d3d-402a-84c1-b2c43065acd8
-- title:
--   Lemma 3.10 — V_i = P_{i_1}⋯P_{i_ℓ}V_leaf, vec(Ŵ_k) = P̂_{k_1}⋯P̂_{k_ℓ}vec(Ŵ_leaf), ∥Ŵ_k∥ ≤ m^{2ℓ}, computable in polynomial time
-- statement:
--   **Lemma 3.10 (Subset-Product Structure).** Let $m\in\mathbb N$, $pp=(W,V)$ with $W,V\in\{0,1\}^{m\times2m^3}$, $[P_0\mid P_1]=VJ_{2m}$, $V_{\mathrm{leaf}}=V(e_1\otimes I_m)$, $\widehat W_{\mathrm{leaf}}=W(e_1\otimes I_m)$, and $[\widehat P_0\mid\widehat P_1]$ the matrix whose $t$-th column is $\mathrm{vec}(W(e_t\otimes I_m))$. For every $\ell\ge0$, $L=2^\ell$, let $V^v_L=\mathrm{Ver}^v(pp,1^L)=[V_1\mid\cdots\mid V_L]$ and $\widehat W_k=\mathrm{Com}^v(pp,e_k)$. Then for all $i,k\in[L]$, with associated bit strings $(i_1,\dots,i_\ell)$ and $(k_1,\dots,k_\ell)$,
--   $$V_i=P_{i_1}\cdots P_{i_\ell}V_{\mathrm{leaf}},\qquad \mathrm{vec}(\widehat W_k)=\widehat P_{k_1}\cdots\widehat P_{k_\ell}\,\mathrm{vec}(\widehat W_{\mathrm{leaf}}),\tag{3.6}$$
--   $\|\widehat W_k\|\le m^{2\ell}$, and, given $pp$ and $i,k\in[L]$, the matrices $V_i$ and $\widehat W_k$ can be computed in time $\mathrm{poly}(m,\ell,\log q)$.
--
--   This expresses each block and basis commitment as a product of $\ell$ matrices, each chosen from a fixed pair by one bit of the index.
--
--   **Formalization Note.** The four clauses are one conjunction. The identities and the norm bound hold for every $m$, $pp$, $\ell$, $i$, $k$; the time clause is one `PolyTimeComputable` algorithm reading $pp$, $\ell$ in unary and $i,k$ as their bit strings, and writing the codes of $V_i$ and $\widehat W_k$. The empty product ($\ell=0$) is the identity.
--
--   Differences from the source:
--   - generalization: time poly(m, ℓ, log q) → time polynomial in the input length, with q not an input; reason: the input (pp, ℓ in unary, i and k as ℓ-bit strings) has length polynomial in m and ℓ and at least m + ℓ, and a bound without log q implies the paper's
--   - encoding: given pp and i, k ∈ [L], compute V_i and Ŵ_k → alg (encParams m pp ++ encNat ℓ ++ encIndex ℓ i ++ encIndex ℓ k) = encSq V_i ++ encSq Ŵ_k for one PolyTimeComputable alg; reason: a fixed bit-string interface for the algorithm; indices are given as their associated bit strings
--   - encoding: indices i, k ∈ [L], bits {0,1}, W, V ∈ {0,1}^{m×2m^3} → 0-based Fin (2^ℓ), Fin 2, Matrix (Fin m) (Col m) (Fin 2) with Col m = Fin 2 × Fin m × Fin m × Fin m; reason: Lean convention; the lexicographic flattenings are the paper's, so the same objects
--   - encoding: ∥Ŵ_k∥ = max over columns of the ℓ∞ norm → entryNorm, the largest natAbs of an entry (0 for no entries); reason: same number
--   - generalization: m ∈ ℕ (lattice parameter) → every m : ℕ, including m = 0 (all matrices empty); reason: the m = 0 instances are trivially true; every instance of the source is covered
-- source:
--   Wee, Wichs, Wu, SNARGs and ABE for Uniform Computations via Lattice Encodings, STOC 2027 submission (manuscript sha256 fd77662e…), p. 22, Lemma 3.10

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_UnifLattice_FastVf_Notation
import Definitions.Def_UnifLattice_FastVf_VectorCommitment
import Definitions.Def_UnifLattice_FastVf_ProofMatrices
import Definitions.Def_UnifLattice_FastVf_Encoding

open Matrix

namespace UnifLattice.FastVf

/-- Lemma 3.10 (Subset-Product Structure), p. 22. For all `m`, all `pp = (W, V)` with
`W, V ∈ {0,1}^{m × 2m³}`, all `ℓ ≥ 0` (`L = 2^ℓ`) and all `i, k ∈ [L]` with associated bit strings
`(i₁, …, i_ℓ)`, `(k₁, …, k_ℓ)`:
`V_i = P_{i₁} ⋯ P_{i_ℓ} V_leaf`, `vec(Ŵ_k) = P̂_{k₁} ⋯ P̂_{k_ℓ} vec(Ŵ_leaf)` (Eq. (3.6)), and
`∥Ŵ_k∥ ≤ m^{2ℓ}`. Moreover one polynomial-time algorithm computes `V_i` and `Ŵ_k` from `pp` and
`i, k` (given as their bit strings, with `ℓ` in unary). -/
theorem lemma_3_10 :
    (∀ (m : ℕ) (pp : CommitParams m) (ℓ : ℕ) (i k : Fin (2 ^ ℓ)),
      blockV pp ℓ i = (List.ofFn fun t => P pp (assocBit ℓ i t)).prod * Vleaf pp ∧
      vec (basisCom pp ℓ k) =
        (List.ofFn fun t => Phat pp (assocBit ℓ k t)).prod *ᵥ vec (Wleaf pp) ∧
      entryNorm (basisCom pp ℓ k) ≤ m ^ (2 * ℓ)) ∧
    ∃ alg : List Bool → List Bool, QAlgorithms.Complexity.PolyTimeComputable alg ∧
      ∀ (m : ℕ) (pp : CommitParams m) (ℓ : ℕ) (i k : Fin (2 ^ ℓ)),
        alg (encParams m pp ++ QAlgorithms.Complexity.encNat ℓ ++ encIndex ℓ i ++ encIndex ℓ k) =
          encSq (blockV pp ℓ i) ++ encSq (basisCom pp ℓ k) := by sorry

end UnifLattice.FastVf
