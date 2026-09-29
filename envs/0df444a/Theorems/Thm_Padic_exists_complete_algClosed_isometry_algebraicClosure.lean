-- Prove2me | Theorems.Thm_Padic_exists_complete_algClosed_isometry_algebraicClosure
-- name    : Padic.exists_complete_algClosed_isometry_algebraicClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/071635b1-f355-5e34-80cd-da7ef3b10f4f
-- title:
--   Existence of ℂₚ with isometric Galois extensions
-- statement:
--   For every prime $p$ there exists a field $K$ (in the lowest universe) carrying the structure of a nontrivially normed field whose distance is ultrametric, which is complete as a uniform space, of characteristic zero, algebraically closed, and a $\mathbb{Q}_p$-algebra, such that two conditions hold. First, the structural map $\mathbb{Q}_p \to K$ is norm-preserving: $\|\,\mathrm{algebraMap}\,x\|=\|x\|$ for all $x \in \mathbb{Q}_p$, so the norm of $K$ extends the $p$-adic absolute value. Second, there is a $\mathbb{Q}_p$-algebra homomorphism $\iota \colon \overline{\mathbb{Q}_p} \to K$ from `AlgebraicClosure ℚ_[p]` into $K$ with the property that every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}_p}$ admits an extension along $\iota$: there is a ring homomorphism $\sigma_K \colon K \to K$ which is an isometry for the metric of $K$ and satisfies $\sigma_K(\iota(x)) = \iota(\sigma(x))$ for all $x \in \overline{\mathbb{Q}_p}$. Note that $\sigma_K$ is only asserted to be an isometric ring endomorphism of $K$, not an automorphism, and that no norm is assumed on `AlgebraicClosure ℚ_[p]` itself.
--
--   This is the existence of the field $\mathbb{C}_p$, the completion of an algebraic closure of $\mathbb{Q}_p$, packaged with exactly the data needed to run the Tate-curve parametrisation over a complete algebraically closed nonarchimedean field of characteristic zero together with a Galois action. It is used in the construction of the torsion of Tate curves and of finite flat prolongations at $p=2$ and $p=3$, where the isometric extension $\sigma_K$ transports the Galois action on $\overline{\mathbb{Q}_p}$-points to $K$-points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Padic_exists_complete_algClosed_isometry_algebraicClosure.lean

import Mathlib
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal

theorem Padic.exists_complete_algClosed_isometry_algebraicClosure
    (p : ℕ) [Fact p.Prime] :
    ∃ (K : Type) (_ : NontriviallyNormedField K) (_ : IsUltrametricDist K)
      (_ : CompleteSpace K) (_ : CharZero K) (_ : IsAlgClosed K) (_ : Algebra ℚ_[p] K),
      (∀ x : ℚ_[p], ‖algebraMap ℚ_[p] K x‖ = ‖x‖) ∧
      ∃ (ι : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] K),
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]),
          ∃ (σK : K →+* K), Isometry ⇑σK ∧ (∀ x, σK (ι x) = ι (σ x)) := by sorry
