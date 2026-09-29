-- Prove2me | Theorems.Thm_PadicAlgCl_exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le
-- name    : PadicAlgCl.exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/47c69abe-ab8e-5988-92b0-141284383da0
-- title:
--   Ax's approximation lemma over ℚ̄ₚ
-- statement:
--   Let $p$ be a natural number carrying the hypothesis that it is prime, and let `PadicAlgCl p` denote the algebraic closure of $\mathbb{Q}_p$ with its norm extending the $p$-adic absolute value. The assertion is the existence of a real constant $c$, with $0 < c$, such that the following holds for every intermediate field $K$ of the extension $\mathbb{Q}_p \subseteq \overline{\mathbb{Q}}_p$, every element $\alpha$ of $\overline{\mathbb{Q}}_p$ and every real number $\delta$: if every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}_p$ belonging to the fixing subgroup of $K$ — that is, fixing each element of $K$ — satisfies $\|\sigma\alpha - \alpha\| \le \delta$, then there exists $a \in K$ with $\|\alpha - a\| \le c\,\delta$. The order of the quantifiers records that $c$ is uniform: it depends only on $p$, and not on $K$, $\alpha$ or $\delta$. No positivity is imposed on $\delta$; taking $\sigma$ to be the identity in the hypothesis forces $\delta \ge 0$ anyway. No bound on the degree of $\alpha$ over $K$, nor any completeness or closedness assumption on $K$, is required.
--
--   This is Ax's approximation lemma: an element of $\overline{\mathbb{Q}}_p$ moved only slightly by the automorphisms fixing $K$ lies correspondingly close to $K$, with a constant depending on $p$ alone (Ax obtains $c = p^{p/(p-1)^2}$, but only its existence is asserted here). It is the main ingredient in the Ax–Sen–Tate theorem, and is used in this development to identify the elements of the $p$-adic complex numbers fixed by the fixing subgroup of $K$ with the closure of $K$, via [`PadicComplex.forall_smul_eq_self_iff_mem_closure`](thm.html#PadicComplex.forall_smul_eq_self_iff_mem_closure).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicAlgCl.exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le
    (p : ℕ) [Fact p.Prime] :
    ∃ c : ℝ, 0 < c ∧
      ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (α : PadicAlgCl p) (δ : ℝ),
        (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup → ‖σ α - α‖ ≤ δ) →
          ∃ a ∈ K, ‖α - a‖ ≤ c * δ := by sorry
