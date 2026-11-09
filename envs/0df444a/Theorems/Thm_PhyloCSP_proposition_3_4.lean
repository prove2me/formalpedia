-- Prove2me | Theorems.Thm_PhyloCSP_proposition_3_4
-- name    : PhyloCSP.proposition_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:24:46.558446+00:00
-- url     : https://prove2.me/theorems/211a90e8-8438-4f47-bfe9-c0851eb8c14b
-- title:
--   Proposition 3.4 — basic transformations are consistent
-- statement:
--   Let $B$ be a template, $p$ a probability distribution on $\mathrm{Loc}(B)$ and $\nu$ a centrally symmetric distribution on $\{\pm1\}^{E(B)}$. Let $T$ be an input tree on a finite leaf set $S$ and $\emptyset\neq A\subseteq S$. Then the output of the basic transformation on $T$, restricted to $A$, has the same law as its output on $T{\restriction}A$: for every relation $R'$ on $A$,
--   $$
--   \sum_{R\,:\,R\restriction A=R'}\Pr\bigl(\text{output on }T=R\bigr)=\Pr\bigl(\text{output on }T{\restriction}A=R'\bigr).
--   $$
--
--   Together with the fact that mixtures of consistent transformations are consistent, this shows that the finite mixtures in Theorem 3.2(ii) are consistent, so their guarantees are computed by eq. (2).
--
--   **Formalization Note** The statement is about the output law on raw ternary relations, so it does not presuppose that outputs are trees.
--
--   Differences from the source:
--   - encoding: F[T]↾A =ᵈ F[T↾A] for the basic transformation (Definition 3.1) → for every relation R′ on A, the total output probability of the relations on S restricting to R′ equals the output probability of R′ on T↾A; reason: equality of the push-forward law under restriction, stated on raw relations
--   - encoding: finite rooted binary trees up to label-preserving isomorphism, arbitrary leaf labels → patterns as rooted-triplet relations satisfying the axioms of Section 7.1 on finite leaf sets S ⊆ ℕ (S = ∅ included, with its single pattern); reason: the paper's own characterization (pp.1, 18); relabeling equivariance makes labels in ℕ cover every tree; the empty leaf set adds no constraint
--   - encoding: a basic transformation (Definition 3.3, steps 1–4, arbitrary ±1 child labels) → the law of the triplet relation of the output for fixed random choices (basicRawLaw), read off the output's clusters, with the child containing the least leaf labeled +1; reason: steps 2–4 determine the output's clusters; p.8 says the law does not depend on the labeling since ν is centrally symmetric
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Proposition 3.4, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_PhyloCSP_basicRawLaw
import Definitions.Def_PhyloCSP_Pattern

set_option autoImplicit false

open scoped ENNReal

namespace PhyloCSP

open Template

/-- Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027
submission (manuscript sha256 3444b6c0…682dac), Proposition 3.4, p.9 (PDF p.11): "Basic
transformations are consistent."

For every template `B`, location law `p` and centrally symmetric orientation law `ν`, every input
tree `T` on `S` and every nonempty `A ⊆ S`, the law of the output restricted to `A` equals the law
of the output on the restricted input `T↾A`: for every relation `R'` on `A`, the total probability
of the output relations on `S` whose restriction to `A` is `R'` equals the probability of `R'` for
the input `T↾A`.

**Formalization Note.** Stated for the output law on raw relations (`basicRawLaw`), so it does not
presuppose that the output is a tree. Restriction is pull-back along the inclusion `↥A ↪ ↥S`. -/
theorem proposition_3_4 (B : Template) (p : PMF B.Loc) (ν : PMF (B.Edge → Bool))
    (hν : IsCentrallySymmetric ν) (S : Finset ℕ) (T : Pattern ↥S) (A : Finset ℕ) (hA : A ⊆ S)
    (hne : A.Nonempty) (R' : ↥A → ↥A → ↥A → Bool) :
    (∑ R ∈ Finset.univ.filter (fun R : ↥S → ↥S → ↥S → Bool =>
        (fun a b c => R (inclEmb hA a) (inclEmb hA b) (inclEmb hA c)) = R'),
      basicRawLaw B p ν T.1 R) =
      basicRawLaw B p ν (T.comap (inclEmb hA)).1 R' := by sorry

end PhyloCSP
