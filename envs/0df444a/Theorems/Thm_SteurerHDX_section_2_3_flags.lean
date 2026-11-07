-- Prove2me | Theorems.Thm_SteurerHDX_section_2_3_flags
-- name    : SteurerHDX.section_2_3_flags
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:48.692949+00:00
-- url     : https://prove2.me/theorems/d964aab0-611a-4f94-977d-788f48354c8d
-- title:
--   Section 2.3: the projected flags complex is a pure partite sparse $2/(\sqrt q-1)$-top-link expander
-- statement:
--   This collects the properties of the Hopkins–Ray projected flags complex stated in Section 2.3.
--
--   There are absolute constants $c_0,c_1,c_2,C>0$ such that the following holds for every finite field $\mathbb F_q$ and all integers $1\le k<r$. Let $\mathcal X=\mathcal X^{S_k}$ be the projected flags complex of $\mathbb F_q^{2r}$ with $S_k=\{r-k,\dots,r+k\}$, and $d=2k+1=|S_k|$. Then:
--
--   1. $\mathcal X$ is a pure $d$-dimensional complex, and it is $d$-partite;
--   2. its facets are exactly the chains $W_1\subset\dots\subset W_d$ with $\{\dim W_i\}=S_k$;
--   3. for every $i\in S_k$ the number of $i$-dimensional vertices lies in $[\,q^{r^2-c_0kr},\ q^{r^2+c_0kr}\,]$;
--   4. the number of vertices satisfies $q^{c_1r^2}\le|\mathcal X(1)|\le q^{c_2r^2}$;
--   5. its degree is at most $q^{Ckr}$;
--   6. it is a $\frac{2}{\sqrt q-1}$-top-link expander: $\lambda_2(\tau)\le\frac{2}{\sqrt q-1}$ for every face $\tau$ of codimension $2$.
--
--   These are the inputs that, through Theorem 2.3 with $\delta=1/2$, give the sparse expanders of Theorem 2.4.
--
--   **Formalization Note** $\Theta(\cdot)$ and $O(\cdot)$ are absolute constants, chosen before the field and before $k,r$.
--
--   Differences from the source:
--   - encoding: q a prime power, F_q^{2r} → a finite field F with q = |F|, vectors Fin (2r) → F; reason: the finite fields are exactly the fields of prime-power order, unique up to isomorphism; same instances
--   - reading: q^{r²±Θ(kr)}, q^{Θ(r²)}, q^{O(kr)} → absolute constants c₀, c₁, c₂, C > 0 chosen before F, k and r; reason: the standard meaning of the asymptotic notation; constants independent of k are the stronger reading
--   - reading: a general k (with S_k ⊆ [2r − 1]) → 1 ≤ k < r; reason: S_k ⊆ [2r − 1] requires k < r, and k ≥ 1 is the setting of Theorem 2.4 (d = 2k + 1); for k = 0 the Θ(kr) error terms degenerate to 0
--   - reading: degree q^{O(kr)} ≈ 2^{O(k√log X(1))}, which is sub-polynomial in the number of vertices → the degree bound q^{Ckr} and the vertex bounds only; reason: the "≈ … sub-polynomial" phrase is an approximate commentary on the two stated bounds, not a separate claim
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Section 2.3, p.4

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_SteurerHDX_IsPartite
import Definitions.Def_SteurerHDX_degree
import Definitions.Def_SteurerHDX_IsTopLinkExpander
import Definitions.Def_SteurerHDX_flagsComplex

namespace SteurerHDX

/-- **Properties of the projected flags complex (Section 2.3).** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Section 2.3, p.4:
"The projected flags complex X^S is the k-partite k-dimensional simplicial complex whose vertices
are the subspaces W ⊂ F_q^{2r} with dim(W) ∈ S, partitioned according to dimension. Its facets are
maximal chains … Observe that there are q^{r²±Θ(kr)} subspaces of dimension i for any i ∈ S …
Fixing k and letting r → ∞, we get a strongly explicit infinite family of complexes with
q^{Θ(r²)} vertices and degree q^{O(kr)} … Furthermore, it is not hard to see λ₂(τ) ≤ 2/(√q − 1)
for any τ of co-dimension 2."

**Formalization Note.** With S = S_k (|S_k| = 2k + 1 = d) and 1 ≤ k < r: the complex is pure
d-dimensional and d-partite (parts = dimensions), its facets are exactly the chains with one
subspace of each dimension in S_k, the number of vertices of each dimension i ∈ S_k lies in
[q^{r² − c₀kr}, q^{r² + c₀kr}], the number of vertices lies in [q^{c₁r²}, q^{c₂r²}], the degree is
at most q^{Ckr}, and it is a 2/(√q − 1)-top-link expander. Θ and O are absolute constants,
chosen before the field F and before k, r. A prime power q is encoded as a finite field `F` with
`Fintype.card F = q`. The decidable-equality instance on subspaces is arbitrary (all agree). -/
theorem section_2_3_flags :
    ∃ c₀ c₁ c₂ C : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < C ∧
    ∀ (F : Type*) [Field F] [Fintype F] (r k : ℕ)
      [DecidableEq (Submodule F (Fin (2 * r) → F))], 1 ≤ k → k < r →
      IsPure (flagsComplex F r k) (2 * k + 1) ∧
      IsPartite (flagsComplex F r k) (2 * k + 1) ∧
      (∀ σ, σ ∈ faces (flagsComplex F r k) (2 * k + 1) ↔
        σ ∈ flagsComplex F r k ∧
          σ.image (fun W : Submodule F (Fin (2 * r) → F) => Module.finrank F W) = Finset.Icc (r - k) (r + k)) ∧
      (∀ i ∈ Finset.Icc (r - k) (r + k),
        (Fintype.card F : ℝ) ^ ((r : ℝ) ^ 2 - c₀ * k * r) ≤
          (((faces (flagsComplex F r k) 1).filter
            (fun s => ∀ W ∈ s, Module.finrank F (W : Submodule F (Fin (2 * r) → F)) = i)).card : ℝ) ∧
        (((faces (flagsComplex F r k) 1).filter
            (fun s => ∀ W ∈ s, Module.finrank F (W : Submodule F (Fin (2 * r) → F)) = i)).card : ℝ) ≤
          (Fintype.card F : ℝ) ^ ((r : ℝ) ^ 2 + c₀ * k * r)) ∧
      (Fintype.card F : ℝ) ^ (c₁ * (r : ℝ) ^ 2) ≤ ((faces (flagsComplex F r k) 1).card : ℝ) ∧
      ((faces (flagsComplex F r k) 1).card : ℝ) ≤ (Fintype.card F : ℝ) ^ (c₂ * (r : ℝ) ^ 2) ∧
      (degree (flagsComplex F r k) (2 * k + 1) : ℝ) ≤
        (Fintype.card F : ℝ) ^ (C * k * r) ∧
      IsTopLinkExpander (flagsComplex F r k) (2 * k + 1)
        (2 / (Real.sqrt (Fintype.card F) - 1)) := by sorry

end SteurerHDX
