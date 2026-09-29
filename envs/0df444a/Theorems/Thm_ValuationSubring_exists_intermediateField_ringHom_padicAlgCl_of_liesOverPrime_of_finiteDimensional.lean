-- Prove2me | Theorems.Thm_ValuationSubring_exists_intermediateField_ringHom_padicAlgCl_of_liesOverPrime_of_finiteDimensional
-- name    : ValuationSubring.exists_intermediateField_ringHom_padicAlgCl_of_liesOverPrime_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/0ee69f87-90ab-5fd4-ad0f-6577c27f410f
-- title:
--   Places of ℚ̄ above p come from p-adic embeddings
-- statement:
--   Let $p$ be a prime, let $O$ be a commutative ring equipped with an algebra structure on $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` (so with a structure map $O \to \overline{\mathbb Q}$), and let $P$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$ in the sense that the image of $p$ in $\overline{\mathbb Q}$ is a non-unit of $P$. Assume the structure map sends every element of $O$ into $P$, and that there is an intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$, finite-dimensional over $\mathbb Q$, containing the image of every element of $O$. Then there exist an intermediate field $K$ of $\overline{\mathbb Q}_p/\mathbb Q_p$ which is finite-dimensional over $\mathbb Q_p$, a ring homomorphism $\iota \colon \overline{\mathbb Q} \to \overline{\mathbb Q}_p$, and a ring homomorphism $\varphi \colon O \to \mathcal O_K$, where $\mathcal O_K$ denotes the $\mathbb Z_p$-subalgebra $\mathrm{integralClosure}\,\mathbb Z_p\,\overline{\mathbb Q}_p \cap K$ of $\overline{\mathbb Q}_p$, such that: the image of $\varphi(x)$ in $\overline{\mathbb Q}_p$ equals $\iota$ of the structure image of $x$, for every $x \in O$; for all $t \in \overline{\mathbb Q}$ one has $P.\mathrm{valuation}\,t < 1$ if and only if $\lVert \iota t\rVert < 1$, and $t \in P$ if and only if $\lVert \iota t \rVert \le 1$; and, for every $\mathbb Q_p$-algebra automorphism $\sigma$ of $\overline{\mathbb Q}_p$ and every $\mathcal O_K$-algebra automorphism $\tau_\ell$ of $\overline{\mathbb Q}_p$ with $\tau_\ell = \sigma$ pointwise, with $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb Q}_p/\mathbb Q_p)$ of the inertia subgroup of the valuation subring [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20) of $\overline{\mathbb Q}_p$, there are a $\mathbb Q$-algebra automorphism $\tau$ and an $O$-algebra automorphism $\tau'$ of $\overline{\mathbb Q}$ which agree pointwise, with $\tau$ in the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$, and $\iota(\tau' t) = \tau_\ell(\iota t)$ for all $t$. Note that $\iota$ is asserted only as a ring homomorphism, and the transfer of inertia is asserted in one direction, from local to global.
--
--   This is the dictionary translating an abstract place of $\overline{\mathbb Q}$ above $p$, together with a number field and a ring of coefficients mapping into the place, into a concrete embedding of $\overline{\mathbb Q}$ into $\overline{\mathbb Q}_p$ matching the valuation, its maximal ideal and (from the local side) inertia; it rests on the conjugacy of the extensions of the $p$-adic valuation to $\overline{\mathbb Q}$. It is used in the global form of the inertia-invariance argument for $p$-divisible groups, in [`PDivisibleGroup.forall_dual_apply_eq_zero_of_forall_valuation_sub_counit_lt_one_of_forall_inertia`](thm.html#PDivisibleGroup.forall_dual_apply_eq_zero_of_forall_valuation_sub_counit_lt_one_of_forall_inertia).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_intermediateField_ringHom_padicAlgCl_of_liesOverPrime_of_finiteDimensional.lean

import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_intermediateField_ringHom_padicAlgCl_of_liesOverPrime_of_finiteDimensional
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F]
    (hOF : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ F) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K)
      (ι : AlgebraicClosure ℚ →+* PadicAlgCl p) (φ : O →+* PadicAlgCl.ringOfIntegers p K),
      (∀ x : O, ((φ x : PadicAlgCl.ringOfIntegers p K) : PadicAlgCl p) = ι (algebraMap O (AlgebraicClosure ℚ) x)) ∧
      (∀ t : AlgebraicClosure ℚ, P.valuation t < 1 ↔ ‖ι t‖ < 1) ∧
      (∀ t : AlgebraicClosure ℚ, t ∈ P ↔ ‖ι t‖ ≤ 1) ∧
      (∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (τl : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ s : PadicAlgCl p, τl s = σ s) → σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∃ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ),
          (∀ t : AlgebraicClosure ℚ, τ' t = τ t) ∧ τ ∈ P.inertiaSubgroupIn ℚ ∧ ∀ t : AlgebraicClosure ℚ, ι (τ' t) = τl (ι t)) := by sorry
