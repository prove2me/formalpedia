-- Prove2me | Theorems.Thm_PhyloCSP_Supplement_theorem_9_5
-- name    : PhyloCSP.Supplement.theorem_9_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:28:59.345819+00:00
-- url     : https://prove2.me/theorems/1618eb3f-f3fc-43cf-a027-b0bd73053fdd
-- title:
--   Theorem 9.5 — one invariant order: colors iid given $\lambda_\xi$, ties broken by convex orders $<_t$
-- statement:
--   Let $<$ be a random linear order on the leaf set $Z$ of the Fraïssé limit $F=(Z,C)$ whose distribution is invariant under every automorphism $g\in\mathrm{Aut}(F)$. Then there exist a random probability distribution $\lambda=\lambda_\xi$ on $[0,1]$, colors $r(x)\in[0,1]$ for $x\in Z$, and, for every atom $t$ of $\lambda$, a relation $<_t$ on $Z$, all given by measurable functions of the order $<$ alone, such that:
--
--   1. **Conditionally iid colors.** Conditional on $\lambda$, the colors $(r(x))_{x\in Z}$ are independent with distribution $\lambda$: for distinct leaves $x_1,\dots,x_n$, Borel sets $A_1,\dots,A_n$ and a measurable set $B$ of distributions,
--   $$
--   \Pr\big(\lambda\in B,\ r(x_i)\in A_i\ \forall i\big)=\mathbb E\Big[\mathbf 1\{\lambda\in B\}\prod_{i=1}^n\lambda(A_i)\Big].
--   $$
--   2. **The order.** Almost surely, for all distinct leaves $x,y$: if $r(x)<r(y)$, or if $r(x)=r(y)=t$ for an atom $t$ of $\lambda$ and $x<_t y$, then $x<y$.
--   3. **Convex tie-breaking orders.** Almost surely, for every atom $t$ of $\lambda$, $<_t$ is a strict total order on $Z$ that is $C$-convex.
--   4. **Equivariance.** For every fixed $g\in\mathrm{Aut}(F)$, almost surely, applying the construction to the order $a<_g b:\iff g(a)<g(b)$ gives the same $\lambda$, the colors $x\mapsto r(g(x))$ and, at every atom $t$, the orders $a\,(<_t)_g\,b:\iff g(a)<_t g(b)$.
--
--   This is the description of a single invariant order on which the classification of invariant transformations of $F$ (Sections 9.3–11) is built.
--
--   **Formalization Note** The setting is that of the published Lemmas 9.2 and 9.4: a measurable map $\omega\mapsto(\,<_\omega\,)\in\{0,1\}^{Z\times Z}$ on a probability space, every realization a strict total order, with law invariant under $\mathrm{Aut}(F)$. The paper's random variable $\xi$ is taken to be $\lambda_\xi$ itself (the directing measure); conditional independence given $\xi$ with law $\lambda_\xi$ is equivalent to conditional independence given $\lambda_\xi$. The values of $<_t$ at non-atoms $t$ are unconstrained.
--
--   Differences from the source:
--   - encoding: a random variable ξ and the distribution λ_ξ → ξ is λ_ξ itself, a measurable function of the order with values in probability measures on ℝ carried by [0, 1]; reason: conditional iid with law λ_ξ given ξ is equivalent to conditional iid given λ_ξ (λ_ξ is a function of ξ, and λ_ξ is a valid ξ)
--   - encoding: conditional on ξ, the colors are iid with distribution λ_ξ → P(λ ∈ B, r(x_i) ∈ A_i for all i) = E[1{λ ∈ B} ∏ λ(A_i)] for all distinct x_1, …, x_n, Borel A_i and measurable B; reason: these finite-dimensional identities determine the joint law of λ and the colors, hence the conditional law
--   - encoding: colors and convex orders deterministically defined by <; a random C-convex order <_t for each atom t → measurable maps r, λ and ord of the realization lt ω; ord(lt ω) t is required (almost surely, at every atom t) to be a strict total C-convex order; reason: a deterministic function of the order is a measurable map of it; the orders are only used at atoms
--   - encoding: applying g to < relabels the colors and the orders <_t by the same g → the maps evaluated at (a, b) ↦ lt ω (g a) (g b) return λ, x ↦ r(g x) and (a, b) ↦ ord t (g a) (g b) at atoms t, almost surely for each fixed g; reason: the same convention as the invariance hypothesis
--   - encoding: a random linear order on Z with Aut(F)-invariant distribution; F → measurable lt : Ω → Z → Z → Bool, every realization a strict total order, P.map of the g-relabelled order equals P.map lt; F is the concrete (Z, fraisseRel) of Definition 7.5; reason: the setting of the published Lemmas 9.2 and 9.4; Theorem 7.4 identifies the concrete structure with F
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Theorem 9.5, p.30 (PDF p.32); construction in Section 9.2, pp.28–29 (PDF pp.30–31); setting of Section 9.1

import Mathlib
import Definitions.Def_PhyloCSP_AutF
import Definitions.Def_PhyloCSP_IsConvexOrder

set_option autoImplicit false

open MeasureTheory

namespace PhyloCSP

namespace Supplement

/-- Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Theorem 9.5 (One invariant order), p.30 (PDF p.32): "Let <
be a random linear order on Z whose distribution is invariant under Aut(F). There exist a random
variable ξ, colors r(x) ∈ [0, 1] for the leaves x ∈ Z, and a random C-convex order <t on Z for
each atom t of a probability distribution λξ, with the following properties. • Conditional on ξ,
the colors (r(x))x∈Z are iid with distribution λξ. • Almost surely, for distinct leaves x, y, we
have x < y if either r(x) < r(y) or, for some atom t of λξ, r(x) = r(y) = t and x <t y. • The
colors and convex orders are deterministically defined by <. For every fixed automorphism g of F,
applying g to < almost surely relabels the colors and the orders <t by the same g, while leaving
λξ unchanged."

Setting (as in the published Lemmas 9.2 and 9.4): a random order `lt ω` on `Z`, measurable as a
map into `Z → Z → Bool`, every realization a strict total order, with the law of
`(a, b) ↦ lt ω (g a) (g b)` equal to the law of `lt` for every `g ∈ Aut(F)`.

The conclusion provides three measurable maps of the order `o : Z → Z → Bool` (so all objects are
"deterministically defined by <"): the color distribution `λ o`, a probability measure on `ℝ`
carried by `[0, 1]`; the colors `r o x ∈ [0, 1]`; and, for each `t`, a relation `ord o t` (the
order `<_t`, used only at atoms `t` of `λ o`). Writing `o = lt ω`:

1. conditional on `λ`, the colors are iid with law `λ`: for distinct leaves `x₁, …, xₙ`, Borel
   sets `A₁, …, Aₙ` and a measurable set `B` of measures,
   `P(λ ∈ B, r(xᵢ) ∈ Aᵢ ∀ i) = E[1{λ ∈ B} ∏ᵢ λ(Aᵢ)]`;
2. almost surely, for distinct `x, y`: if `r x < r y`, or `r x = r y = t` for an atom `t` of `λ`
   with `x <_t y`, then `x < y`;
3. almost surely, for every atom `t`, `<_t` is a strict total order on `Z` that is `C`-convex;
4. for every `g ∈ Aut(F)`, almost surely the maps applied to the order `(a, b) ↦ lt ω (g a) (g b)`
   give the same `λ`, the colors `x ↦ r (g x)` and, at every atom `t`, the order
   `(a, b) ↦ (g a <_t g b)`.

**Formalization Note.** The random variable `ξ` is taken to be `λ_ξ` itself, the directing measure
of the exchangeable colors: conditional independence given `ξ` with law `λ_ξ` implies it given
`λ_ξ`, and conversely, so nothing is lost. "Conditional on ξ, iid" is stated through the joint law
of `λ` and finitely many colors, which determines the conditional law. -/
theorem theorem_9_5 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (lt : Ω → Z → Z → Bool) (hmeas : Measurable lt)
    (horder : ∀ ω, IsStrictTotalOrder Z (fun a b => lt ω a b = true))
    (hinv : ∀ g ∈ AutF, P.map (fun ω a b => lt ω (g a) (g b)) = P.map lt) :
    ∃ (lam : (Z → Z → Bool) → Measure ℝ) (r : (Z → Z → Bool) → Z → ℝ)
      (ord : (Z → Z → Bool) → ℝ → Z → Z → Bool),
      Measurable lam ∧ Measurable r ∧ Measurable ord ∧
      (∀ o, IsProbabilityMeasure (lam o) ∧ lam o (Set.Icc 0 1) = 1) ∧
      (∀ o x, r o x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ (n : ℕ) (x : Fin n ↪ Z) (A : Fin n → Set ℝ), (∀ i, MeasurableSet (A i)) →
        ∀ B : Set (Measure ℝ), MeasurableSet B →
          P {ω | lam (lt ω) ∈ B ∧ ∀ i, r (lt ω) (x i) ∈ A i} =
            ∫⁻ ω in {ω | lam (lt ω) ∈ B}, ∏ i, lam (lt ω) (A i) ∂P) ∧
      (∀ᵐ ω ∂P, ∀ x y : Z, x ≠ y →
        (r (lt ω) x < r (lt ω) y ∨
          ∃ t : ℝ, lam (lt ω) {t} ≠ 0 ∧ r (lt ω) x = t ∧ r (lt ω) y = t ∧
            ord (lt ω) t x y = true) →
        lt ω x y = true) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ, lam (lt ω) {t} ≠ 0 →
        IsStrictTotalOrder Z (fun a b => ord (lt ω) t a b = true) ∧
          IsConvexOrder fraisseRel (fun a b => ord (lt ω) t a b = true)) ∧
      (∀ g ∈ AutF, ∀ᵐ ω ∂P,
        lam (fun a b => lt ω (g a) (g b)) = lam (lt ω) ∧
          (∀ x : Z, r (fun a b => lt ω (g a) (g b)) x = r (lt ω) (g x)) ∧
          ∀ t : ℝ, lam (lt ω) {t} ≠ 0 → ∀ a b : Z,
            ord (fun a b => lt ω (g a) (g b)) t a b = ord (lt ω) t (g a) (g b)) := by sorry

end Supplement

end PhyloCSP
