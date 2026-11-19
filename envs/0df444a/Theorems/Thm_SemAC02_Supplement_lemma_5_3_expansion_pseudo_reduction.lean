-- Prove2me | Theorems.Thm_SemAC02_Supplement_lemma_5_3_expansion_pseudo_reduction
-- name    : SemAC02.Supplement.lemma_5_3_expansion_pseudo_reduction
-- status  : Proved
-- author  : @Henry Yuen
-- created : 2026-11-18T09:44:03.749356+00:00
-- url     : https://prove2.me/theorems/98f2c051-6454-4b6a-b71d-16ba217b0c67
-- title:
--   Lemma 5.3: expansion pseudo-reduction operator (explicit s ≥ 1)
-- statement:
--   Let $F=F_0\cup\bigcup_{u\in L}F_u$ be a finite clustered polynomial representation over $\mathbb F_2$, with its variables partitioned into right clusters. Assume the representation is respectful, the background axioms have a common Boolean zero, all axioms are multilinear of degree at most $K$, and its incidence graph is an $(s,c)$ boundary expander, where $s\ge1$, $c>0$, and $K+1\le cs/2$. Fix a degree-compatible monomial order, and let $R(t)$ be the local normal form modulo the background axioms and the axiom clusters in $\operatorname{Sup}_s(N(t))$.
--
--   The linear extension to Boolean polynomials of degree at most $K$ is a pseudo-reduction operator: it annihilates the axioms, does not increase degree, fixes $1$, and satisfies
--
--   $$
--   R(p)=0\quad\Longrightarrow\quad R(xp)=0
--   $$
--
--   whenever $xp$ has degree at most $K$. For each $k\le K$, its image dimension is the dimension of the span of the local normal forms of background-standard monomials of degree at most $k$.
--
--   This supplies the expansion operator used in the random-formula and graph-pigeonhole lower bounds.
--
--   **Formalization Note** The statement includes $s\ge1$ explicitly because the mission's expansion parameters are real-valued. Without this convention, the original statement has a vacuous-expansion counterexample for $0<s<1$. The polynomial representative is defined on all multilinear monomials and factors through the background quotient; its rank is computed on the standard monomial basis.
-- source:
--   Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, Hard Instances for Strong Semantic Proof Systems, Definition 5.2 and Lemma 5.3, printed p.39; rank representation in Definition 5.2 and §5.2. https://www.doc.ic.ac.uk/~itzamere/Reslin_Simplification.pdf. Explicit s ≥ 1 repairs the real-valued parameter corner case. Construction checked against Mikša–Nordström, A Generalized Method for Proving Polynomial Calculus Degree Lower Bounds, JACM 71(6), 2024, Observation 2.10, Lemmas 4.29–4.33 and proof of Theorem 4.11, https://jakobnordstrom.se/docs/publications/GeneralizedMethodPCdegree_JACM.pdf.

import Mathlib
import Definitions.Def_SemAC02_Supplement_expansionRank
import Definitions.Def_SemAC02_Supplement_IsPseudoRed
open MvPolynomial AC02Frege SemAC02 SemAC02.Supplement

theorem SemAC02.Supplement.lemma_5_3_expansion_pseudo_reduction {σ L T : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype T] [DecidableEq T]
    (P : ClusteredRep σ L T) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (hml : ∀ p∈P.axioms, IsMultilinear p)
    (hzero : ∃ y : σ → Bool, ∀ g∈P.F0, eval (toF2 y) g=0)
    (hP : P.IsRespectful) (s c : ℝ) (hs : 1 ≤ s) (hc : 0 < c)
    (hexp : IsBdryExp P.graph s c) (K : ℕ)
    (hdeg : ∀ p∈P.axioms, p.totalDegree ≤ K) (hK : (K : ℝ)+1 ≤ c*s/2) :
    ∃ R : Ble σ K →ₗ[ZMod 2] MvPolynomial σ (ZMod 2),
      IsPseudoRed P.axioms R ∧
      (∀ p : Ble σ K, (R p).totalDegree ≤ (p : MvPolynomial σ (ZMod 2)).totalDegree) ∧
      (∀ (t : Finset σ) (ht : t.card ≤ K),
        R ⟨xMon t,Submodule.subset_span ⟨t,ht,rfl⟩⟩=expOp P m s t) ∧
      (∀ k : ℕ, k ≤ K → rankLe R k=expRank P m s k) ∧
      R ⟨xMon ∅,Submodule.subset_span ⟨∅,Nat.zero_le K,rfl⟩⟩=1 := by sorry
