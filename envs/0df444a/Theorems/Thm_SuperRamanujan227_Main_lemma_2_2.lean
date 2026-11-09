-- Prove2me | Theorems.Thm_SuperRamanujan227_Main_lemma_2_2
-- name    : SuperRamanujan227.Main.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:35:45.361207+00:00
-- url     : https://prove2.me/theorems/65b60e0f-2aa0-4664-ac87-59b871d115dc
-- title:
--   Lemma 2.2 — multiplicative interlacing under permutation conjugation
-- statement:
--   Let $A,B$ be real symmetric $m\times m$ matrices, at least one of which is positive semidefinite, and let $P$ be a uniformly random $m\times m$ permutation matrix. Then the expected characteristic polynomial $\mathbb E_P[\chi_x(APBP^{\mathsf T})]$ is real-rooted, and for every $1\le k\le m$ there is a permutation matrix $S$ such that $ASBS^{\mathsf T}$ has only real eigenvalues and
--   $$\lambda_k\big(ASBS^{\mathsf T}\big)\le\alpha_k\Big(\mathbb E_P\big[\chi_x(APBP^{\mathsf T})\big]\Big).$$
--   The permutation $S$ may depend on $k$.
--
--   This is the multiplicative analogue of the Marcus–Spielman–Srivastava interlacing-family lemma; it reduces the existence of a good graph to bounding a root of an expected characteristic polynomial.
--
--   Differences from the source:
--   - reading: λ_k(ASBSᵀ) and α_k(E_P[χ_x(APBPᵀ)]), notations §2.1 defines only for matrices with real eigenvalues and real-rooted polynomials → the conclusion also asserts that E_P[χ_x(APBPᵀ)] and χ_x(ASBSᵀ) are real-rooted; reason: the lemma's use of α_k and λ_k presupposes both; stating them excludes the junk value of α_k
--   - encoding: every k ≤ m → every k with 1 ≤ k ≤ m; reason: λ_k and α_k are 1-based; k = 0 has no meaning
--   - encoding: P uniformly random permutation matrix; E_P in coefficient space → average of the polynomials over all m! permutations σ of the permutation matrix of σ; reason: σ ↦ permutation matrix is a bijection, so this is the uniform distribution
-- source:
--   Gil Cohen, Gal Maor, Quantitative Results on Super-Ramanujan Graphs, STOC 2027 submission #227 (October 2026), SHA-256 1ba5eacb267c8a63eff5e5b9d6b96d9f2b04d5a1e147d887b9e61574127831f8, Lemma 2.2, p. 7, Eq. (2)

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Spectra
open Polynomial

namespace SuperRamanujan227.Main

/-- Lemma 2.2 (p. 7): for real symmetric `A, B`, one of them positive semidefinite, the expected
characteristic polynomial `E_P[χ_x(A P B Pᵀ)]` over a uniformly random permutation matrix is
real-rooted, and for every `1 ≤ k ≤ m` some permutation matrix `S` has `A S B Sᵀ` with real
eigenvalues and `λ_k(A S B Sᵀ) ≤ α_k(E_P[χ_x(A P B Pᵀ)])`. -/
theorem lemma_2_2 {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsSymm) (hB : B.IsSymm)
    (hpsd : A.PosSemidef ∨ B.PosSemidef) :
    RealRooted (expCharpolyMul A B) ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ m → ∃ σ : Equiv.Perm (Fin m),
        RealRooted (A * permMat σ * B * (permMat σ).transpose).charpoly ∧
          matrixEig (A * permMat σ * B * (permMat σ).transpose) k ≤
            kthLargestRoot (expCharpolyMul A B) k := by sorry

end SuperRamanujan227.Main
