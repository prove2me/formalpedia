-- Prove2me | Theorems.Thm_ValuationSubring_exists_padicInt_forall_apply_eq_pow_appr_mul_of_pow_eq_of_residue_eq
-- name    : ValuationSubring.exists_padicInt_forall_apply_eq_pow_appr_mul_of_pow_eq_of_residue_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/f8d1124a-46a8-539e-a5aa-408a5f1dd021
-- title:
--   Tame ℓ-adic exponent of an automorphism fixing π
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, and $\ell$ a prime whose image in the residue field $\mathrm{ResidueField}(A)$ of the local ring $A$ is a unit. Let $\zeta \colon \mathbb{N} \to L$ be a family with $\zeta_k$ a primitive $\ell^k$-th root of unity for every $k$, compatible in the sense that $\zeta_{k+1}^{\ell} = \zeta_k$; let $\pi \in L$ with $\pi \neq 0$; and let $\sigma$ be a ring automorphism of $L$ (an isomorphism of $L$ with itself respecting addition and multiplication) such that $\sigma(\pi) = \pi$ and such that for every $a \in A$ with $\sigma(a) \in A$ the element $\sigma(a)$, viewed in $A$, has the same image as $a$ under the residue map $A \to \mathrm{ResidueField}(A)$; no hypothesis that $\sigma$ preserves $A$ is imposed. The assertion is that there exists an $\ell$-adic integer $t \in \mathbb{Z}_\ell$ with two properties: first, for every $k \in \mathbb{N}$ and every $r \in L$ with $r^{\ell^k} = \pi$ one has $\sigma(r) = \zeta_k^{\,a_k} \, r$, where $a_k =$ `t.appr k` is the natural-number approximation of $t$ modulo $\ell^k$; and second, $t$ is a unit of $\mathbb{Z}_\ell$ if and only if there is some $r \in L$ with $r^{\ell} = \pi$ and $\sigma(r) \neq r$.
--
--   This is the tame $\ell$-adic character attached to $\sigma$ by Kummer theory applied to the system of $\ell$-power roots of $\pi$, formulated for an abstract algebraically closed valued field and a single automorphism that fixes $\pi$ and acts trivially on residues, relative to the chosen generator $(\zeta_k)$ of $\mathbb{Z}_\ell(1)$. It feeds the construction of the monodromy exponent used in the analysis of semistable coverings of curves, and is cited by [`AlgebraicCurve.exists_linearMap_forall_sub_one_eq_smul_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel`](thm.html#AlgebraicCurve.exists_linearMap_forall_sub_one_eq_smul_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_padicInt_forall_apply_eq_pow_appr_mul_of_pow_eq_of_residue_eq.lean

import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_padicInt_forall_apply_eq_pow_appr_mul_of_pow_eq_of_residue_eq
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A))
    (ζ : ℕ → L) (hζ : ∀ k, IsPrimitiveRoot (ζ k) (ℓ ^ k)) (hζc : ∀ k, ζ (k + 1) ^ ℓ = ζ k)
    (π : L) (hπ0 : π ≠ 0)
    (σ : L ≃+* L) (hσπ : σ π = π)
    (hσres : ∀ (a : A) (h : σ (a : L) ∈ A), IsLocalRing.residue A ⟨σ (a : L), h⟩ = IsLocalRing.residue A a) :
    ∃ t : ℤ_[ℓ], (∀ (k : ℕ) (r : L), r ^ (ℓ ^ k) = π → σ r = ζ k ^ (t.appr k) * r) ∧
      (IsUnit t ↔ ∃ r : L, r ^ ℓ = π ∧ σ r ≠ r) := by sorry
