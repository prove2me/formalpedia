-- Prove2me | Theorems.Thm_SuperRamanujan227_Main_lemma_2_5
-- name    : SuperRamanujan227.Main.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:35:53.599367+00:00
-- url     : https://prove2.me/theorems/4b2aca61-e042-44d1-969a-6e3f87809f39
-- title:
--   Lemma 2.5 — quadrature for permutation-conjugated sums and products
-- statement:
--   Let $A,B$ be real symmetric $m\times m$ matrices with $A\mathbf 1=a\mathbf 1$ and $B\mathbf 1=b\mathbf 1$ for real numbers $a,b$, and let $p_A,p_B$ be the polynomials with
--   $$\chi_x(A)=(x-a)\,p_A(x),\qquad \chi_x(B)=(x-b)\,p_B(x).$$
--   Let $P$ be a uniformly random $m\times m$ permutation matrix. Then, with both convolutions taken in degree $m-1$,
--   $$\mathbb E_P\big[\chi_x(A+PBP^{\mathsf T})\big]=(x-(a+b))\,(p_A\boxplus_{m-1}p_B)(x),$$
--   $$\mathbb E_P\big[\chi_x(APBP^{\mathsf T})\big]=(x-ab)\,(p_A\boxtimes_{m-1}p_B)(x).$$
--   Moreover $p_A\boxplus_{m-1}p_B$ is real-rooted, and if at least one of $p_A,p_B$ has only nonnegative roots then $p_A\boxtimes_{m-1}p_B$ is real-rooted.
--
--   This quadrature identity replaces the Haar average defining the finite free convolutions by an average over permutation matrices, which do have a combinatorial meaning; $a,b$ are arbitrary real row sums.
--
--   Differences from the source:
--   - encoding: ⊞ and ⊠ of Definition 2.4 (Haar averages over the orthogonal group) → the MSS coefficient formulas in degree m − 1; reason: the coefficient formulas agree with the Haar averages on characteristic polynomials [MSS22], the paper refers to them on p. 8; p_A, p_B have degree m − 1
--   - encoding: p_A, p_B the polynomials satisfying χ_x(A) = (x − a)p_A(x), χ_x(B) = (x − b)p_B(x) → polynomials pA, pB given with these defining equations as hypotheses; reason: the quotient is unique since ℝ[x] is a domain; the hypotheses are satisfiable exactly when m ≥ 1, as the source presupposes
--   - encoding: real-rooted; only nonnegative roots → nonzero with natDegree-many real roots; every real root is ≥ 0; reason: p_A, p_B are real-rooted (A, B symmetric), so their real roots are all their roots
-- source:
--   Gil Cohen, Gal Maor, Quantitative Results on Super-Ramanujan Graphs, STOC 2027 submission #227 (October 2026), SHA-256 1ba5eacb267c8a63eff5e5b9d6b96d9f2b04d5a1e147d887b9e61574127831f8, Lemma 2.5, p. 8, Eqs. (3)–(4)

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Spectra
import Definitions.Def_SuperRamanujan227_Main_FiniteFreeConvolution
open Polynomial Matrix

namespace SuperRamanujan227.Main

/-- Lemma 2.5 (Quadrature, p. 8): for real symmetric `m × m` matrices with `A𝟙 = a𝟙`, `B𝟙 = b𝟙`
and `χ_x(A) = (x - a) p_A`, `χ_x(B) = (x - b) p_B`, the permutation averages of `χ_x(A + PBPᵀ)`
and `χ_x(APBPᵀ)` are `(x - (a+b)) (p_A ⊞ p_B)` and `(x - ab) (p_A ⊠ p_B)` (convolutions in
degree `m - 1`); `p_A ⊞ p_B` is real-rooted, and so is `p_A ⊠ p_B` when `p_A` or `p_B` has only
nonnegative roots. -/
theorem lemma_2_5 {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsSymm) (hB : B.IsSymm)
    (a b : ℝ) (hA1 : A *ᵥ (fun _ => (1 : ℝ)) = a • (fun _ => (1 : ℝ)))
    (hB1 : B *ᵥ (fun _ => (1 : ℝ)) = b • (fun _ => (1 : ℝ)))
    (pA pB : ℝ[X]) (hpA : A.charpoly = (X - C a) * pA) (hpB : B.charpoly = (X - C b) * pB) :
    expCharpolyAdd A B = (X - C (a + b)) * ffAdd (m - 1) pA pB ∧
      expCharpolyMul A B = (X - C (a * b)) * ffMul (m - 1) pA pB ∧
      RealRooted (ffAdd (m - 1) pA pB) ∧
      ((∀ x ∈ pA.roots, 0 ≤ x) ∨ (∀ x ∈ pB.roots, 0 ≤ x) →
        RealRooted (ffMul (m - 1) pA pB)) := by sorry

end SuperRamanujan227.Main
