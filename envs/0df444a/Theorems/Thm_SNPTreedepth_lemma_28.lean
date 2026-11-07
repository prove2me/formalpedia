-- Prove2me | Theorems.Thm_SNPTreedepth_lemma_28
-- name    : SNPTreedepth.lemma_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:28:54.168322+00:00
-- url     : https://prove2.me/theorems/04b8eba6-6346-4fbc-a7f3-754232cdd768
-- title:
--   Lemma 28 — properties (1)–(8) of the $s$-multiplicity structure $R^s$
-- statement:
--   Let $s\ge p\ge1$ and let $R$ be a relational structure with treedepth decomposition $T$ of height $h$; $R^s$ is the $s$-multiplicity structure for $(R,T,p)$ with tree $T^s$.
--
--   1. $T^s$ is a treedepth decomposition of $R^s$ of height $h$.
--   2. A tuple of retained elements lies in a relation of $R^s$ iff it lies in that relation in $R$.
--   3. Every element $y$ of $R^s$ has in $(R^s,T^s)$ the vertex $p$-type that $\mathrm{orig}(y)$ has in $(R,T)$; in particular $y$ is $p$-abundant iff $\mathrm{orig}(y)$ is.
--   4. In $T^s$ every vertex $y$ has exactly $s$ children of each type that is $p$-abundant in $p\text{-type}(y)$, and as many children of every other type as $\mathrm{orig}(y)$ has in $T$.
--   5. Every element of $R^p$ is retained and has the same $p$-route in $T^p$ as in $T$; hence every tuple of elements of $R^p$ has the same $p$-route pattern in $T^p$ as in $T$.
--   6. If $p\ge z\cdot h$, then for every $z$-tuple of elements of $R$ the realizing vertices of its pattern are retained in $R^p$.
--   7. If $p\ge z\cdot h$, a $p$-route pattern of a $z$-tuple occurs in $(R,T)$ iff it occurs in $(R^p,T^p)$.
--   8. There is a computable $f$ such that $|R^s|\le f(h,p,s)$ for every SNP Model Checking instance $(R,\varphi)$ with $p\ge|\varphi|$.
--
--   These are all the facts about $R^s$ that the extension theorem, Lemma 9, Lemma 32 and the running-time analysis use.
--
--   **Formalization Note** A retained element $y$ is identified with $\mathrm{orig}(y)\in V(R)$. Clauses (1)–(7) are one conjunct for all $R$, $T$, $p$, $s$; clause (8) is a second conjunct with $f$ (computable, uncurried) chosen before every instance.
--
--   Differences from the source:
--   - generalization: z ∈ ℕ (z ≥ 1, as 0 ∉ ℕ, p.13) in (6) and (7) → every z ≥ 0; reason: for z = 0 both clauses are trivial; the statement specializes to z ≥ 1
--   - encoding: R^s built by the copy procedure of Definition 26, fresh elements in an arbitrary order → R^s on addresses (root path of (type, index) entries), relation tuples = chains of T^s whose originals lie in E_i; fresh elements ordered by original and address code; reason: the same tree and relations with copies named by position (argued in the module); the order among fresh elements is arbitrary in the paper
--   - encoding: retained elements are elements of R → retained addresses are the p-routes in T of their originals, identified with orig(y); reason: Definition 27
--   - encoding: a computable function f in (8) → Computable of the uncurried f : ℕ → ℕ → ℕ → ℕ, chosen before every instance; reason: same statement
--   - encoding: an SNP sentence under the conventions of pp.15–16 (negations only before atoms, every R_j, x_i and E_i occurs, positive arities) → Sentence.WellFormed as a hypothesis, NNF built into the syntax; reason: the paper assumes these without loss of generality; they are part of what an SNP Model Checking instance is
-- source:
--   Depian, Ganian, Greilhuber, Gründel, Wietheger, A Uniform Algorithm for Strict NP on Bounded-Treedepth Structures, STOC 2027 submission (manuscript sha256 98e4e1a9…), Lemma 28, p.25 (PDF p.26)

import Mathlib
import Definitions.Def_SNPTreedepth_Structure
import Definitions.Def_SNPTreedepth_Sentence
import Definitions.Def_SNPTreedepth_treedepth
import Definitions.Def_SNPTreedepth_ptype
import Definitions.Def_SNPTreedepth_mult

set_option autoImplicit false

namespace SNPTreedepth

/-- **Lemma 28** (Depian, Ganian, Greilhuber, Gründel, Wietheger, *A Uniform Algorithm for Strict NP on
Bounded-Treedepth Structures*, STOC 2027 submission (manuscript sha256 98e4e1a9…), p.25 (PDF p.26)): "Let s, p ∈ ℕ with s ≥ p ≥ 1, and let R be a
relational structure with treedepth decomposition T of height h.
(1) T^s is a treedepth decomposition of R^s of height h.
(2) A tuple of retained elements lies in a relation of R^s if and only if it lies in that relation
in R.
(3) Every element y of R^s has in (R^s, T^s) the vertex p-type that orig(y) has in (R, T); in
particular y is p-abundant in (R^s, T^s) if and only if orig(y) is p-abundant in (R, T).
(4) In T^s, every vertex y has exactly s children of each vertex p-type that is p-abundant in
p-type(y), and as many children of every other vertex p-type as orig(y) has in T.
(5) Every element of R^p is retained and has the same p-route in T^p as in T; in particular every
tuple of elements of R^p has the same p-route pattern in T^p as in T.
(6) Let z ∈ ℕ with p ≥ z · h. Then for every z-tuple of elements of R, the realizing vertices of its
p-route pattern in T are retained in R^p.
(7) Let z ∈ ℕ with p ≥ z · h. Then a p-route pattern of a z-tuple occurs in (R, T) if and only if it
occurs in (R^p, T^p).
(8) If (R, φ) is an SNP Model Checking instance with p ≥ |φ|, then |R^s| ≤ f(h, p, s) for a
computable function f."

**Formalization Note** The first conjunct collects (1)–(7) for every finite non-empty totally
ordered `R` and treedepth decomposition `T`; the second is (8), with the computable `f` (uncurried,
`Computable`) chosen before every instance. A retained element `y` is identified with the element
`orig(y)` of `R`. In (6) and (7) every `z ≥ 0` is allowed (for `z = 0` both are trivial). -/
theorem lemma_28 :
    (∀ (σ : Signature) (V : Type) [Fintype V] [LinearOrder V] [Nonempty V]
      (R : Structure σ V) (T : RootedForest V), IsTDDecomp R T → ∀ (p s : ℕ), 1 ≤ p → p ≤ s →
      -- (1)
      (IsTDDecomp (mult R T p s) (multTree R T p s) ∧
        (multTree R T p s).height = T.height) ∧
      -- (2)
      (∀ (i : Fin σ.b) (u : Fin (σ.ar i) → MultElem R T p s), (∀ j, Retained (u j)) →
        (u ∈ (mult R T p s).rel i ↔ (fun j => orig (u j)) ∈ R.rel i)) ∧
      -- (3)
      (∀ y : MultElem R T p s,
        ptype (mult R T p s) (multTree R T p s) p y = ptype R T p (orig y) ∧
        (IsAbundantVertex (mult R T p s) (multTree R T p s) p y ↔
          IsAbundantVertex R T p (orig y))) ∧
      -- (4)
      (∀ (y : MultElem R T p s) (t : ℕ),
        (AbundantIn p t (ptype (mult R T p s) (multTree R T p s) p y) →
          typeCount (mult R T p s) (multTree R T p s) p y t = s) ∧
        (¬ AbundantIn p t (ptype (mult R T p s) (multTree R T p s) p y) →
          typeCount (mult R T p s) (multTree R T p s) p y t = typeCount R T p (orig y) t)) ∧
      -- (5)
      ((∀ y : MultElem R T p p, Retained y ∧
          route (mult R T p p) (multTree R T p p) p y = route R T p (orig y)) ∧
        ∀ (z : ℕ) (v : Fin z → MultElem R T p p),
          pattern (mult R T p p) (multTree R T p p) p v = pattern R T p (fun m => orig (v m))) ∧
      -- (6)
      (∀ z : ℕ, z * T.height ≤ p → ∀ (v w : Fin z → V),
        IsRealizing R T p (pattern R T p v) w →
          ∀ m, ∃ y : MultElem R T p p, Retained y ∧ orig y = w m) ∧
      -- (7)
      (∀ z : ℕ, z * T.height ≤ p → ∀ μ : Fin z → List (ℕ × ℕ),
        PatternOccurs R T p μ ↔ PatternOccurs (mult R T p p) (multTree R T p p) p μ)) ∧
    -- (8)
    (∃ f : ℕ → ℕ → ℕ → ℕ, Computable (fun x : ℕ × ℕ × ℕ => f x.1 x.2.1 x.2.2) ∧
      ∀ (σ : Signature) (φ : Sentence σ), φ.WellFormed →
      ∀ (V : Type) [Fintype V] [LinearOrder V] [Nonempty V]
        (R : Structure σ V) (T : RootedForest V), IsTDDecomp R T → ∀ (p s : ℕ), 1 ≤ p → p ≤ s →
        φ.length ≤ p → (mult R T p s).size ≤ f T.height p s) := by sorry

end SNPTreedepth
