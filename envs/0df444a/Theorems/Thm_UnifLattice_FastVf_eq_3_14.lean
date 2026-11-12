-- Prove2me | Theorems.Thm_UnifLattice_FastVf_eq_3_14
-- name    : UnifLattice.FastVf.eq_3_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:21:03.505526+00:00
-- url     : https://prove2.me/theorems/d7f25ac2-5da3-427d-9c79-090bbf1898d2
-- title:
--   Eq. (3.14) — v_g = Σ_b (sᵀ⊗I)(M_{1,b_1}⊗F_{1,b_1})⋯(t⊗r) = (sᵀ⊗I)(Σ_b M_{1,b}⊗F_{1,b})⋯(Σ_b M_{3ℓ,b}⊗F_{3ℓ,b})(t⊗r)
-- statement:
--   **Eq. (3.14)** (displayed in the proof of Theorem 3.13). Let $(\pi,\{M_{\tau,b}\},s,t)$ be an ordered read-once branching program of width $w$ computing $g$, and $v_g=\sum_{i,j,k\in[L]}g(i,j,k)\,\mathrm{vec}(V_i)\otimes\mathrm{vec}(V_j)\otimes\mathrm{vec}(\widehat W_k)\in\mathbb Z^{m^6}$ (Eq. (3.10)). Then
--   $$v_g=\sum_{b\in\{0,1\}^{3\ell}}(s^{\mathsf T}\otimes I_{m^6})(M_{1,b_1}\otimes F_{1,b_1})\cdots(M_{3\ell,b_{3\ell}}\otimes F_{3\ell,b_{3\ell}})(t\otimes r)=(s^{\mathsf T}\otimes I_{m^6})\Big(\sum_{b\in\{0,1\}}M_{1,b}\otimes F_{1,b}\Big)\cdots\Big(\sum_{b\in\{0,1\}}M_{3\ell,b}\otimes F_{3\ell,b}\Big)(t\otimes r).$$
--
--   The right-hand side is a product of $3\ell+2$ matrices of dimension $\mathrm{poly}(m,w)$, which is what makes $V_f$ computable in time polynomial in $\ell$ rather than in $L$.
--
--   **Formalization Note.** Both equalities are stated. $g$ is the program's own value `B.value` (see the differences); $s^{\mathsf T}\otimes I_{m^6}$ is `replicateRow Unit B.sz ⊗ₖ 1`, whose row index is `Unit × K6 m`.
--
--   Differences from the source:
--   - generalization: g computed by BP_g (Correctness: g(i,j,k) = sᵀM_{1,z_{π(1)}}⋯M_{3ℓ,z_{π(3ℓ)}}t ∈ {−1,0,1}), v_g of Eq. (3.10) → v_g formed with the program's own value B.value for every ordered program B, without the Correctness clause; reason: under Correctness g = B.value, so the paper's identity is the special case
--   - encoding: (sᵀ ⊗ I_{m^6}) ∈ Z^{m^6×wm^6}, sums over b ∈ {0,1}^{3ℓ} → rows indexed by Unit × K6 m (v_g read on that index), b : Fin (3 * B.ℓ) → Fin 2; reason: Lean convention; same objects
--   - encoding: positions and steps 1, …, 3ℓ; indices i, j, k ∈ [L] → 0-based Fin (3 * ℓ), Fin (2^ℓ); reason: index shift
--   - generalization: m ∈ ℕ (lattice parameter) → every m : ℕ, including m = 0 (all matrices empty); reason: the m = 0 instances are trivially true; every instance of the source is covered
-- source:
--   Wee, Wichs, Wu, SNARGs and ABE for Uniform Computations via Lattice Encodings, STOC 2027 submission (manuscript sha256 fd77662e…), p. 26, Eq. (3.14) (proof of Theorem 3.13), with Eq. (3.10) p. 25

import Mathlib
import Definitions.Def_UnifLattice_FastVf_Notation
import Definitions.Def_UnifLattice_FastVf_VectorCommitment
import Definitions.Def_UnifLattice_FastVf_QuadraticCommitment
import Definitions.Def_UnifLattice_FastVf_ROBP
import Definitions.Def_UnifLattice_FastVf_ProofMatrices

open Matrix
open scoped Kronecker

namespace UnifLattice.FastVf

/-- Eq. (3.14), p. 26 (proof of Theorem 3.13), with `v_g` of Eq. (3.10) for `g` the value of the
ordered branching program `B = (π, {M_{τ,b}}, s, t)`:
`v_g = Σ_{b ∈ {0,1}^{3ℓ}} (sᵀ ⊗ I_{m⁶})(M_{1,b₁} ⊗ F_{1,b₁}) ⋯ (M_{3ℓ,b_{3ℓ}} ⊗ F_{3ℓ,b_{3ℓ}})(t ⊗ r)
     = (sᵀ ⊗ I_{m⁶}) (Σ_{b ∈ {0,1}} M_{1,b} ⊗ F_{1,b}) ⋯ (Σ_{b ∈ {0,1}} M_{3ℓ,b} ⊗ F_{3ℓ,b}) (t ⊗ r)`.
The row index of `sᵀ ⊗ I_{m⁶}` is `Unit × [m⁶]`. -/
theorem eq_3_14 (m : ℕ) (pp : CommitParams m) (B : ROBP) (hB : B.Ordered) :
    (fun q : Unit × K6 m => vg pp B.ℓ B.value q.2) =
        ∑ b : Fin (3 * B.ℓ) → Fin 2,
          ((replicateRow Unit B.sz ⊗ₖ (1 : Matrix (K6 m) (K6 m) ℤ)) *
            (List.ofFn fun τ => B.Mz τ (b τ) ⊗ₖ F pp B.ℓ B.π τ (b τ)).prod) *ᵥ
              kron B.tz (r pp) ∧
      ∑ b : Fin (3 * B.ℓ) → Fin 2,
          ((replicateRow Unit B.sz ⊗ₖ (1 : Matrix (K6 m) (K6 m) ℤ)) *
            (List.ofFn fun τ => B.Mz τ (b τ) ⊗ₖ F pp B.ℓ B.π τ (b τ)).prod) *ᵥ
              kron B.tz (r pp) =
        ((replicateRow Unit B.sz ⊗ₖ (1 : Matrix (K6 m) (K6 m) ℤ)) *
            (List.ofFn fun τ => ∑ b : Fin 2, B.Mz τ b ⊗ₖ F pp B.ℓ B.π τ b).prod) *ᵥ
          kron B.tz (r pp) := by sorry

end UnifLattice.FastVf
