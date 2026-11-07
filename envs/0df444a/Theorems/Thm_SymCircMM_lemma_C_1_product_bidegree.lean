-- Prove2me | Theorems.Thm_SymCircMM_lemma_C_1_product_bidegree
-- name    : SymCircMM.lemma_C_1_product_bidegree
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:30:34.203703+00:00
-- url     : https://prove2.me/theorems/39420e23-c78a-4c74-840d-3b85e70b986b
-- title:
--   Lemma C.1 — the $(1,1)$-part of a product $u_1\cdots u_m$ and its rank $\le m+1$
-- statement:
--   Let $u_1,\dots,u_m$ be polynomials in the variables $A_{ij},B_{j\ell}$, let $g=u_1\cdots u_m$, and write $c_i$, $L_i$, $M_i$ for the bidegree $(0,0)$, $(1,0)$, $(0,1)$ parts of $u_i$. Then:
--
--   1. the $(1,1)$-part of $g$ is
--   $$g^{(1,1)}=\sum_{i=1}^m\Bigl(\prod_{j\ne i}c_j\Bigr)u_i^{(1,1)}+\sum_{i\ne i'}\Bigl(\prod_{j\ne i,i'}c_j\Bigr)L_iM_{i'};$$
--   2. when every $c_i\ne0$, with $P=\prod_jc_j$,
--   $$\sum_{i\ne i'}\Bigl(\prod_{j\ne i,i'}c_j\Bigr)L_iM_{i'}=P\Bigl(\sum_i\frac{L_i}{c_i}\Bigr)\Bigl(\sum_i\frac{M_i}{c_i}\Bigr)-P\sum_i\frac{L_iM_i}{c_i^2};$$
--   3. the off-diagonal sum is a bilinear form of rank at most $m+1$: it is a sum of at most $m+1$ products of a linear form in the $A$'s and a linear form in the $B$'s, for every choice of the $u_i$;
--   4. if a permutation $\sigma$ acting by (2) permutes $u_1,\dots,u_m$, then it fixes $\bigl(\sum_iL_i/c_i\bigr)\bigl(\sum_iM_i/c_i\bigr)$ and permutes the products $L_iM_i$ among themselves.
--
--   This is the step of Proposition 4.2 that turns a product gate of fan-in $m$ into at most $m+1$ bilinear products.
--
--   **Formalization Note** $f^{(a,b)}$ is the weighted homogeneous component for the bidegree weight, and $c_i$ is the constant coefficient of $u_i$. In item 4, $\sigma\cdot u_i=u_{\pi(i)}$ for a permutation $\pi$ of the indices.
--
--   Differences from the source:
--
--   - encoding: the bidegree (a, b) part f^{(a,b)} and the scalars c_i → MvPolynomial.weightedHomogeneousComponent bideg (a, b) and c_i = the constant coefficient of u_i; reason: the (0, 0) part of a polynomial is its constant term
--   - encoding: a bilinear form of rank at most m + 1 → ∃ t ≤ m + 1 and (1,0)-forms L′_s, (0,1)-forms M′_s with the off-diagonal sum = ∑_s L′_s M′_s; reason: the rank of a bilinear form is the least number of such products
--   - reading: "If σ ∈ G fixes g then it permutes u_1, …, u_m" → the hypothesis σ · u_i = u_{π(i)} for all i, for a permutation π of the indices; reason: fixing a gate and permuting its children are circuit facts; on the polynomials they say exactly this
--   - generalization: the σ-invariance of (∑_i L_i/c_i)(∑_i M_i/c_i), stated for the right-hand side of the identity that assumes every c_i ≠ 0 → stated for every u, with Lean's convention c⁻¹ = 0 when c_i = 0; reason: when every c_i ≠ 0 it is the paper's claim; otherwise π still preserves each c_i, so the invariance holds as well
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Lemma C.1, p.19 (PDF p.20)

import Mathlib
import Definitions.Def_SymCircMM_MMVar

set_option autoImplicit false

namespace SymCircMM

/-- **Lemma C.1** (Dahan, Dawar, Kush, Pago, *Symmetric Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), p.19 (PDF p.20)). Let `g = u₁ ⋯ u_m` and write `c_i, L_i, M_i` for the
bidegree `(0,0)`, `(1,0)`, `(0,1)` parts of `u_i`. Then
`g^{(1,1)} = ∑_i (∏_{j≠i} c_j) u_i^{(1,1)} + ∑_{i≠i′} (∏_{j≠i,i′} c_j) L_i M_{i′}`; the second sum is a
bilinear form of rank at most `m + 1`; when every `c_i ≠ 0`, with `P = ∏_j c_j`, it equals
`P (∑_i L_i/c_i)(∑_i M_i/c_i) − P ∑_i L_i M_i/c_i²`; and if `σ` permutes `u₁, …, u_m`, the product
`(∑_i L_i/c_i)(∑_i M_i/c_i)` is `σ`-invariant and the products `L_i M_i` are permuted among themselves.

**Formalization Note.** Polynomials in `F[A, B]` (`MMVar ι`); `f^{(a,b)}` is the weighted homogeneous
component for `bideg`, and `c_i` (the `(0,0)` part) is the constant coefficient. The rank claim is
the existence of at most `m + 1` products of an `A`-linear and a `B`-linear form summing to the
off-diagonal part, for every `u` (vanishing `c_i` included). "σ fixes g, hence permutes the `u_i`" is
taken as the hypothesis that renaming by (2) sends each `u_i` to `u_{π i}` for a permutation `π`. -/
theorem lemma_C_1_product_bidegree {ι F : Type} [Fintype ι] [Field F] {m : ℕ}
    (u : Fin m → MvPolynomial (MMVar ι) F) :
    let comp : ℕ × ℕ → MvPolynomial (MMVar ι) F → MvPolynomial (MMVar ι) F :=
      fun d p => MvPolynomial.weightedHomogeneousComponent bideg d p
    let c : Fin m → F := fun i => MvPolynomial.coeff 0 (u i)
    let L : Fin m → MvPolynomial (MMVar ι) F := fun i => comp (1, 0) (u i)
    let M : Fin m → MvPolynomial (MMVar ι) F := fun i => comp (0, 1) (u i)
    let off : MvPolynomial (MMVar ι) F := ∑ i, ∑ i' ∈ Finset.univ.erase i,
      MvPolynomial.C (∏ j ∈ (Finset.univ.erase i).erase i', c j) * L i * M i'
    let SL : MvPolynomial (MMVar ι) F := ∑ i, MvPolynomial.C (c i)⁻¹ * L i
    let SM : MvPolynomial (MMVar ι) F := ∑ i, MvPolynomial.C (c i)⁻¹ * M i
    (comp (1, 1) (∏ i, u i) =
        ∑ i, MvPolynomial.C (∏ j ∈ Finset.univ.erase i, c j) * comp (1, 1) (u i) + off) ∧
    ((∀ i, c i ≠ 0) → off = MvPolynomial.C (∏ j, c j) * (SL * SM) -
        MvPolynomial.C (∏ j, c j) * ∑ i, MvPolynomial.C (c i ^ 2)⁻¹ * (L i * M i)) ∧
    (∃ t ≤ m + 1, ∃ L' M' : Fin t → MvPolynomial (MMVar ι) F,
        (∀ s, MvPolynomial.IsWeightedHomogeneous bideg (L' s) (1, 0)) ∧
        (∀ s, MvPolynomial.IsWeightedHomogeneous bideg (M' s) (0, 1)) ∧
        off = ∑ s, L' s * M' s) ∧
    (∀ (σ : Equiv.Perm ι) (π : Equiv.Perm (Fin m)),
        (∀ i, MvPolynomial.rename (mmAct σ) (u i) = u (π i)) →
        MvPolynomial.rename (mmAct σ) (SL * SM) = SL * SM ∧
        ∀ i, MvPolynomial.rename (mmAct σ) (L i * M i) = L (π i) * M (π i)) := by sorry

end SymCircMM
