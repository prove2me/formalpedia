-- Prove2me | Theorems.Thm_ReadTwiceCount_private_literal
-- name    : ReadTwiceCount.private_literal
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:52.033456+00:00
-- url     : https://prove2.me/theorems/b404b4da-3af3-4c09-905d-71f3d1a91397
-- title:
--   §8 (39)–(41) — private literals: $y_j=Z_{j-1}/Z_j$ and $Z(F)=2^M\prod_j 1/y_j$
-- statement:
--   Let $F$ be a satisfiable read-twice normalized formula on $M$ variables with clauses $C_1,\dots,C_n$, $n\ge1$. Let $F_j$ be the conjunction of the first $j$ clauses on the same universe and $Z_j=Z(F_j)$, so $Z_0=2^M$. For each $j$ introduce a fresh private variable $h_j$ and define
--   $$H_j=F_{j-1}\wedge(C_j\vee h_j).$$
--   Then $H_j$ is read-twice, $h_j$ is a dangling query of $H_j$,
--   $$p(H_j,h_j)=\frac{Z_j}{Z_{j-1}+Z_j}>0,\qquad y_j:=y(H_j,h_j)=\frac{Z_{j-1}}{Z_j},$$
--   and
--   $$Z(F)=2^M\prod_{j=1}^n\frac1{y_j}.$$
--
--   This reduces counting to $n$ marginal queries, each answered by the marginal procedure.
--
--   Differences from the source:
--   - encoding: a fresh private variable $h_j$ for each $j$ → the new last variable of the universe `Fin (M + 1)`, as the positive literal, in every $H_j$; reason: each $H_j$ is a separate formula containing one private variable; $Z_j$ is over `Fin M` and $Z(H_j)$ over `Fin (M + 1)`
--   - encoding: the clauses "in any deterministic order" $C_1,\dots,C_n$ → the order of the clause list of $F$; reason: the statement is for every formula, hence for every ordering of its clauses
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), §8, displays (39)–(41), p.14

import Mathlib
import Definitions.Def_ReadTwiceCount_pFalse

namespace ReadTwiceCount

/-- **The private-literal reduction (39)–(41)** (He, *A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments*, STOC 2027
submission (manuscript sha256 7a2a9dcd…), §8,
displays (39)–(41), p.14). Let `F` be a satisfiable read-twice normalized formula with clauses `C₁, …, C_n`,
`n ≥ 1`, let `F_j` be the conjunction of the first `j` clauses on the same universe and
`Z_j = Z(F_j)`. Add a fresh variable `h_j` (the new variable `M` of the universe `Fin (M + 1)`) and
put `H_j = F_{j−1} ∧ (C_j ∨ h_j)` (39). Then `H_j` is read-twice, `h_j` is a dangling query of
`H_j`, `p(H_j, h_j) = Z_j/(Z_{j−1} + Z_j) > 0` and `y_j := y(H_j, h_j) = Z_{j−1}/Z_j` (40), and
`Z(F) = 2^M ∏_{j=1}^n 1/y_j` (41).

**Formalization Note** `F` is the normalized formula of §8. One fresh variable serves every `H_j`,
since each `H_j` is a separate formula. The counts `Z_j` are over the universe `Fin M`, `Z(H_j)` over `Fin (M + 1)`. -/
theorem private_literal {M : ℕ} (F : Formula M) (hRT : ReadTwice F) (hN : Normalized F)
    (hZ : 0 < Z F)
    (hn : 1 ≤ F.clauses.length) :
    let n := F.clauses.length
    let Fj : ℕ → Formula M := fun j => ⟨F.clauses.take j⟩
    let lift : List (Lit M) → List (Lit (M + 1)) := List.map fun l => (l.1.castSucc, l.2)
    let hj : Lit (M + 1) := (Fin.last M, true)
    let Hj : ℕ → Formula (M + 1) := fun j =>
      ⟨(F.clauses.take (j - 1)).map lift ++ [lift (F.clauses.getD (j - 1) []) ++ [hj]]⟩
    (∀ j, 1 ≤ j → j ≤ n →
        ReadTwice (Hj j) ∧ IsDangling (Hj j) hj ∧
          pFalse (Hj j) hj = (Z (Fj j) : ℚ) / ((Z (Fj (j - 1)) : ℚ) + Z (Fj j)) ∧
          0 < pFalse (Hj j) hj ∧
          yCoord (Hj j) hj = (Z (Fj (j - 1)) : ℚ) / Z (Fj j)) ∧
      (Z F : ℚ) = 2 ^ M * ∏ j ∈ Finset.Icc 1 n, 1 / yCoord (Hj j) hj := by sorry

end ReadTwiceCount
