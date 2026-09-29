-- Prove2me | Theorems.Thm_ValuationSubring_exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime
-- name    : ValuationSubring.exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/b662843b-e976-513f-b19f-e3386f3bba79
-- title:
--   ℚᵣ as the closure of ℚ in widehatℚ̄_A
-- statement:
--   Let $r$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` such that the image of $r$ in $\overline{\mathbb{Q}}$ lies in `A.nonunits`, i.e. has $A$-valuation $<1$ (equivalently, lies in the maximal ideal of $A$), and let $v$ be a height-one prime of the ring of integers $\mathcal{O}_{\mathbb{Q}}$ containing the image of $r$. Write $C_A$ for the completion `A.valuation.Completion` of $\overline{\mathbb{Q}}$ for the valuation of $A$, and let `ratClosure A` be the topological closure in $C_A$ of the bottom subfield $\bot$ of $C_A$, that is, of the image of $\mathbb{Q}$. The assertion is that there is a ring isomorphism $e$ from the $v$-adic completion of $\mathbb{Q}$ onto `ratClosure A` with three properties: (i) for every $q \in \mathbb{Q}$, the element $e$ of the image of $q$ in the $v$-adic completion equals, as an element of $C_A$, the image of $q \in \overline{\mathbb{Q}}$ in $C_A$; (ii) an element $x$ of the $v$-adic completion lies in `v.adicCompletionIntegers ℚ` if and only if $e(x)$ lies in the valuation subring of the valuation of $C_A$ restricted along the inclusion of `ratClosure A`; (iii) both $e$ and $e^{-1}$ are continuous.
--
--   This is the identification of the $r$-adic field $\mathbb{Q}_r$, with its ring of integers and its topology, with the closure of $\mathbb{Q}$ inside the completion of $\overline{\mathbb{Q}}$ at a place lying over $r$. It is the transport device used in the Čerednik–Drinfel'd material, where the Bruhat–Tits tree and lattice vocabulary over $(\mathcal{O}_v, \mathbb{Q}_v)$ is moved to the closure of $\mathbb{Q}$ in $C_A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField ValuationSubring

theorem ValuationSubring.exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ e : v.adicCompletion ℚ ≃+* ↥(ratClosure A),
      (∀ q : ℚ, ((e (algebraMap ℚ (v.adicCompletion ℚ) q) : ↥(ratClosure A)) : A.valuation.Completion) =
        ((q : AlgebraicClosure ℚ) : A.valuation.Completion)) ∧
      (∀ x : v.adicCompletion ℚ,
        x ∈ v.adicCompletionIntegers ℚ ↔ e x ∈ (Valued.v.comap (ratClosure A).subtype).valuationSubring) ∧
      Continuous e ∧ Continuous e.symm := by sorry
