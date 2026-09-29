-- Prove2me | Theorems.Thm_ValuationSubring_exists_mulSemiringAction_integralClosure_inf_fixedPoints_of_isDiscreteValuationRing
-- name    : ValuationSubring.exists_mulSemiringAction_integralClosure_inf_fixedPoints_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/90f34c3a-1d75-56dc-927c-e234b1eb0a56
-- title:
--   Discrete place under a finite group action: Dedekind data
-- statement:
--   Let $F$ be a field carrying a faithful action of a finite group $G$ by ring automorphisms, and let $P$ be a valuation subring of $F$ whose underlying ring is a discrete valuation ring. Write $R := P \cap F^{G}$ for the intersection of the subring of $P$ with the subfield of $G$-fixed points, and $S :=$ the integral closure of $R$ in $F$. The assertion is that there exist an action of $G$ on $S$ by ring automorphisms and an ideal $\mathfrak{P}$ of $S$ such that: the inclusion $S \to F$ is $G$-equivariant; $R$ is a discrete valuation ring and a Dedekind domain; an element $x \in F$ is $G$-fixed if and only if $x = a/b$ in the sense that $xb = a$ for some $a, b \in R$ with $b \neq 0$; $S$ is a Dedekind domain, module-finite and torsion-free over $R$, with $F$ as its fraction field, and the $G$-action exhibits $G$ as a Galois group of $S$ over $R$ in the sense of Mathlib's `IsGaloisGroup`; every element of $S$ lies in $P$; $\mathfrak{P}$ is maximal, its contraction to $R$ is maximal and non-zero and consists exactly of the elements of $R$ that are non-units of $P$; $\mathfrak{P}$ consists exactly of the elements of $S$ that are non-units of $P$; and every $e \in P$ is of the form $s/t$ with $s, t \in S$ and $t \notin \mathfrak{P}$, i.e. $P = S_{\mathfrak{P}}$.
--
--   This packages the classical local theory of a discrete place in a Galois extension — the integral closure of the fixed discrete valuation ring, its Dedekind and finiteness properties, and the maximal ideal centred at the given place — in the form of a single existential supplying the hypotheses needed by the results on inertia groups and ramification indices. It is used in the analysis of ramification on modular curves, notably in the computation of inertia at places of the function fields of $X_0$ and $X_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_mulSemiringAction_integralClosure_inf_fixedPoints_of_isDiscreteValuationRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem ValuationSubring.exists_mulSemiringAction_integralClosure_inf_fixedPoints_of_isDiscreteValuationRing
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] [MulSemiringAction G F] [FaithfulSMul G F]
    (P : ValuationSubring F) [IsDiscreteValuationRing ↥P] :
    ∃ (_ : MulSemiringAction G
          ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F))
      (𝔓 : Ideal ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F)),

      (∀ (g : G) (s : ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F)),
          g • algebraMap ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F s = algebraMap ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F (g • s)) ∧

      IsDiscreteValuationRing ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) ∧
      IsDedekindDomain ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) ∧
      (∀ x : F, x ∈ FixedPoints.subfield G F ↔
          ∃ a b : ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring), (b : F) ≠ 0 ∧ x * (b : F) = (a : F)) ∧

      IsDedekindDomain ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) ∧
      Module.Finite ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)
        ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) ∧
      Module.IsTorsionFree ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)
        ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) ∧
      IsFractionRing ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F ∧
      IsGaloisGroup G ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)
        ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) ∧

      (∀ s : ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F), algebraMap ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F s ∈ P) ∧

      𝔓.IsMaximal ∧
      (𝔓.comap (algebraMap ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)
          ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F))).IsMaximal ∧
      𝔓.comap (algebraMap ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F)) ≠ ⊥ ∧
      (∀ r : ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring),
          r ∈ 𝔓.comap (algebraMap ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)
            ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F)) ↔ (r : F) ∈ P.nonunits) ∧
      (∀ s : ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F),
          algebraMap ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F s ∈ P.nonunits ↔ s ∈ 𝔓) ∧

      (∀ e : ↥P, ∃ s t : ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F),
          t ∉ 𝔓 ∧ (e : F) * algebraMap ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F t = algebraMap ↥(integralClosure ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) F) F s) := by sorry
