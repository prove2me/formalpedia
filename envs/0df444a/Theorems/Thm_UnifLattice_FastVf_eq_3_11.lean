-- Prove2me | Theorems.Thm_UnifLattice_FastVf_eq_3_11
-- name    : UnifLattice.FastVf.eq_3_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:21:03.077207+00:00
-- url     : https://prove2.me/theorems/68b3b052-7a06-4877-a47a-0acd1c582985
-- title:
--   Eq. (3.11) — vec(V_i) ⊗ vec(V_j) ⊗ vec(Ŵ_k) = F_{1,z_{π(1)}}⋯F_{3ℓ,z_{π(3ℓ)}} r for an ordered reading order π
-- statement:
--   **Eq. (3.11)** (displayed in the proof of Theorem 3.13). Let $\pi$ be a reading order of $[3\ell]$ satisfying the Ordering clause of Definition 3.11. For all $(i,j,k)\in[L]^3$, with $z\in\{0,1\}^{3\ell}$ the bit string associated with $(i,j,k)$,
--   $$\mathrm{vec}(V_i)\otimes\mathrm{vec}(V_j)\otimes\mathrm{vec}(\widehat W_k)=F_{1,z_{\pi(1)}}F_{2,z_{\pi(2)}}\cdots F_{3\ell,z_{\pi(3\ell)}}\,r,$$
--   where $F_{\tau,b}=(I_m\otimes P_b)\otimes I_{m^2}\otimes I_{m^2}$ if $\pi(\tau)\le\ell$, $I_{m^2}\otimes(I_m\otimes P_b)\otimes I_{m^2}$ if $\ell<\pi(\tau)\le2\ell$, $I_{m^2}\otimes I_{m^2}\otimes\widehat P_b$ if $\pi(\tau)>2\ell$, and $r=\mathrm{vec}(V_{\mathrm{leaf}})\otimes\mathrm{vec}(V_{\mathrm{leaf}})\otimes\mathrm{vec}(\widehat W_{\mathrm{leaf}})$.
--
--   It interleaves the three subset products of Lemma 3.10 into one product in the program's reading order; the Ordering clause is needed (for an unordered $\pi$ the factors appear out of order).
--
--   **Formalization Note.** $P_b,\widehat P_b,V_{\mathrm{leaf}},\widehat W_{\mathrm{leaf}},F,r$ are those of the ProofMatrices item; the product is in step order.
--
--   Differences from the source:
--   - generalization: π the reading order of BP_g (an ordered read-once branching program computing g) → any permutation π of [3ℓ] satisfying the Ordering clause of Definition 3.11; reason: Eq. (3.11) involves only π; the reading order of every ordered program satisfies the Ordering clause
--   - encoding: positions 1, …, 3ℓ, cases π(τ) ≤ ℓ, ℓ < π(τ) ≤ 2ℓ, π(τ) > 2ℓ → 0-based Fin (3 * ℓ), cases π τ < ℓ, ℓ ≤ π τ < 2ℓ, 2ℓ ≤ π τ; reason: index shift; same cases
--   - encoding: vectors in Z^{m^6}, matrices in Z^{m^6×m^6} → functions on K6 m = ((Fin m × Fin m) × (Fin m × Fin m)) × (Fin m × Fin m), Kronecker products left-associated; reason: the lexicographic flattening is the paper's
--   - generalization: m ∈ ℕ (lattice parameter) → every m : ℕ, including m = 0 (all matrices empty); reason: the m = 0 instances are trivially true; every instance of the source is covered
-- source:
--   Wee, Wichs, Wu, SNARGs and ABE for Uniform Computations via Lattice Encodings, STOC 2027 submission (manuscript sha256 fd77662e…), p. 25, Eq. (3.11) (proof of Theorem 3.13)

import Mathlib
import Definitions.Def_UnifLattice_FastVf_Notation
import Definitions.Def_UnifLattice_FastVf_VectorCommitment
import Definitions.Def_UnifLattice_FastVf_ROBP
import Definitions.Def_UnifLattice_FastVf_ProofMatrices

open Matrix

namespace UnifLattice.FastVf

/-- Eq. (3.11), p. 25 (proof of Theorem 3.13): for every reading order `π` of `[3ℓ]` satisfying the
Ordering clause of Definition 3.11 and all `(i, j, k) ∈ [L]³` with associated bit string `z`,
`vec(V_i) ⊗ vec(V_j) ⊗ vec(Ŵ_k) = F_{1, z_{π(1)}} F_{2, z_{π(2)}} ⋯ F_{3ℓ, z_{π(3ℓ)}} r`. -/
theorem eq_3_11 (m : ℕ) (pp : CommitParams m) (ℓ : ℕ) (π : Equiv.Perm (Fin (3 * ℓ)))
    (hπ : IsOrderedPerm ℓ π) (i j k : Fin (2 ^ ℓ)) :
    kron (kron (vec (blockV pp ℓ i)) (vec (blockV pp ℓ j))) (vec (basisCom pp ℓ k)) =
      (List.ofFn fun τ => F pp ℓ π τ (assocString ℓ i j k (π τ))).prod *ᵥ r pp := by sorry

end UnifLattice.FastVf
