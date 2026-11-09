-- Prove2me | Theorems.Thm_ResultantVNP_lemma_3_3
-- name    : ResultantVNP.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:35:04.157963+00:00
-- url     : https://prove2.me/theorems/9568910f-346b-493a-8428-b50847a3adda
-- title:
--   Lemma 3.3 — the permanent as a grid assignment sum
-- statement:
--   For an $n\times n$ matrix $Z=(z_{ij})$ ($n\ge1$) the construction $A_m(Z)$ of Appendix A.1 on the grid of side $m=m(n)$ satisfies:
--
--   1. $m=3^r+1$ with $r\ge1$, $m>n$, and $m=O(n)$: there is a constant $C$ with $m(n)\le Cn$ for all $n\ge1$;
--   2. it is constructible in polynomial time: the map $n\mapsto$ the entry table of $A_m(Z)$ (entries coded as $0$, $1$ or $z_{ij}$), with $n$ given in unary, is computable by a Turing machine in polynomial time;
--   3. $A_m(Z)$ is a symmetric tensor supported on the grid triangles, with five indices per class and entries in $\{0,1\}\cup\{z_{ij}:i,j\in[n]\}$;
--   4. $H_m(A_m(Z))=\mathrm{per}(Z)$ as polynomials in the $z_{ij}$ (Eq. (5));
--   5. the construction preserves the count on $0/1$ inputs: for every $0/1$ matrix $Z$, every assignment of $H_m(A_m(Z))$ has weight $0$ or $1$, and the number of weight-$1$ assignments equals the number of permutations $\sigma$ with $z_{i\sigma(i)}=1$ for all $i$, i.e. the number of perfect matchings of the bipartite graph of $Z$.
--
--   The lemma turns the permanent, which is VNP-complete, into a grid assignment sum, which Lemma 3.7 extracts from $\Phi_{n,s}$.
--
--   **Formalization Note** The permanent is Mathlib's $\sum_\sigma\prod_i z_{\sigma(i)i}$, the same polynomial as $\sum_\sigma\prod_i z_{i\sigma(i)}$. Turing machines are Mathlib's multi-stack machines (`TM2ComputableInPolyTime`), input $n$ in unary, output the bit string `gridTableCode n`.
--
--   Differences from the source:
--   - reading: one can construct a symmetric tensor A_m(Z) … such that (5) → the statement is about the specific construction A_m(Z) of Appendix A.1 (gridTensor n); reason: Lemma 3.3 names A_m(Z), and Appendix A.1 defines it; the existential claim follows
--   - reading: one can construct in polynomial time → n ↦ gridTableCode n (the symbolic entry table, entries coded 0, 1 or z_ij) is TM2ComputableInPolyTime from unary n to bit strings; reason: the construction does not depend on the values of Z; any concrete Z is substituted entry by entry
--   - reading: the construction preserves the count on 0/1 inputs → for every 0/1 matrix Z, every assignment has weight 0 or 1 and the number of weight-1 assignments equals #{σ : ∀ i, Z i (σ i) = 1}; reason: Appendix A.1: nonzero-weight assignments correspond bijectively to perfect matchings of the matrix's bipartite graph
--   - encoding: m = O(n) → ∃ C, ∀ n ≥ 1, gridSide n ≤ C·n; reason: the meaning of O(n)
--   - encoding: n × n matrix Z → the generic matrix with variables z_{ij}, n ≥ 1, indices Fin n × Fin n; reason: Lean convention; per(Z) of a concrete Z is the evaluation
--   - encoding: index classes of A_m(Z) (five per position) → class map Prod.fst on GridIdx m = (ZMod m × ZMod m) × GridState; reason: Appendix A.1 uses a separate copy of the five states at each position
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Lemma 3.3, Eq. (5), p.15; proof in Appendix A.1, p.37

import Mathlib
import Definitions.Def_ResultantVNP_SupportedOnGrid
import Definitions.Def_ResultantVNP_gridTableCode

namespace ResultantVNP

/-- **Lemma 3.3 (Permanent as a grid assignment sum).** Given an `n × n` matrix `Z = (z_{ij})`, one can
construct in polynomial time a symmetric tensor `A_m(Z)` supported on the grid triangles of side
`m = m(n) = 3^r + 1 = O(n)`, with `r ≥ 1`, five indices per class, and entries in
`{0, 1} ∪ {z_{ij} : i, j ∈ [n]}`, such that `H_m(A_m(Z)) = per(Z)`. The construction preserves the count
on `0/1` inputs.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Lemma 3.3, Eq. (5), p.15 (proof Appendix A.1, p.37).

**Formalization Note** `A_m(Z)` is the construction of Appendix A.1 (`gridTensor n`, for the generic
matrix with variables `z_{ij}`, indices `Fin n × Fin n`), with index classes the five indices at each
position (class map `Prod.fst`). The clauses are:
(a) `m(n) = O(n)`: one constant `C` with `m(n) ≤ C·n` for `n ≥ 1`;
(b) "in polynomial time": the map `n ↦` the entry table of `A_m(Z)` (`gridTableCode`, entries coded as
`0`, `1` or `z_{ij}`), with `n` in unary, is computable by a Turing machine (Mathlib's `TM2` model) in
polynomial time;
(c) for every `n ≥ 1`: `m = 3^r + 1` with `r ≥ 1` and `m > n`; support on the grid triangles; five indices
per class; entries in `{0, 1} ∪ {z_{ij}}`; `H_m(A_m(Z)) = per(Z)` as polynomials (Mathlib's permanent
`∑_σ ∏_i z_{σ(i), i}`, the same polynomial as `∑_σ ∏_i z_{i,σ(i)}`);
(d) "preserves the count on 0/1 inputs": for every `0/1` matrix `Z`, every assignment has weight
`0` or `1`, and the number of weight-`1` assignments equals the number of permutations `σ` with
`Z_{i,σ(i)} = 1` for all `i` (perfect matchings of the bipartite graph of `Z`). -/
theorem lemma_3_3 :
    (∃ C : ℕ, ∀ n, 1 ≤ n → gridSide n ≤ C * n) ∧
    Nonempty (Turing.TM2ComputableInPolyTime Computability.unaryEncodeNat id gridTableCode) ∧
    ∀ n, 1 ≤ n →
      (∃ r, 1 ≤ r ∧ gridSide n = 3 ^ r + 1) ∧ n < gridSide n ∧
      SupportedOnGrid (fun α : GridIdx (gridSide n) => α.1) (gridTensor n) ∧
      (∀ p : ZMod (gridSide n) × ZMod (gridSide n),
        Fintype.card {α : GridIdx (gridSide n) // α.1 = p} = 5) ∧
      (∀ T, gridTensor n T = 0 ∨ gridTensor n T = 1 ∨ ∃ ij, gridTensor n T = MvPolynomial.X ij) ∧
      gridSum (fun α : GridIdx (gridSide n) => α.1) (gridTensor n) =
        (Matrix.of fun i j : Fin n => (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) ℤ)).permanent ∧
      ∀ Z : Matrix (Fin n) (Fin n) ℤ, (∀ i j, Z i j = 0 ∨ Z i j = 1) →
        (∀ ν : (∀ p, {α : GridIdx (gridSide n) // α.1 = p}),
          MvPolynomial.eval (fun ij => Z ij.1 ij.2)
              (∏ p, gridTensor n (assignTriple (fun α => α.1) ν p)) = 0 ∨
            MvPolynomial.eval (fun ij => Z ij.1 ij.2)
              (∏ p, gridTensor n (assignTriple (fun α => α.1) ν p)) = 1) ∧
        Fintype.card {ν : (∀ p, {α : GridIdx (gridSide n) // α.1 = p}) //
            MvPolynomial.eval (fun ij => Z ij.1 ij.2)
              (∏ p, gridTensor n (assignTriple (fun α => α.1) ν p)) = 1} =
          Fintype.card {σ : Equiv.Perm (Fin n) // ∀ i, Z i (σ i) = 1} := by sorry

end ResultantVNP
