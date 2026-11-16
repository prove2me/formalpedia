-- Prove2me | Theorems.Thm_PathRecording_Supplement_theorem_5_9
-- name    : PathRecording.Supplement.theorem_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:34:02.069231+00:00
-- url     : https://prove2.me/theorems/b65931f1-9787-4620-8142-762d30c2aad7
-- title:
--   Theorem 5.9 — Schur orthogonality for semisimple algebras, $\sum_\sigma\rho_\lambda(\sigma)_{ab}\,\rho_\mu(\sigma^*)_{cd}=\delta_{\lambda\mu}\delta_{ad}\delta_{bc}/d_\lambda$
-- statement:
--   Let $A$ be a finite-dimensional semisimple complex algebra with a basis $B(A)=\{\sigma_i\}$. For $a\in A$ let $\mathrm{tr}(a)$ be the trace of the regular representation (left multiplication by $a$ on $A$), and let $\sigma_i^*$ be the dual elements under this trace, $\mathrm{tr}(\sigma_i^*\sigma_j)=\delta_{ij}$. Let $\lambda,\mu\in\Lambda(A)$ label two simple modules $V^\lambda_A,V^\mu_A$ with bases, carrying the representations $\rho_\lambda,\rho_\mu$, and let $|a\rangle,|b\rangle\in B(V^\lambda_A)$, $|c\rangle,|d\rangle\in B(V^\mu_A)$. Then
--   $$\sum_{\sigma\in B(A)}\langle a|\rho_\lambda(\sigma)|b\rangle\,\langle c|\rho_\mu(\sigma^*)|d\rangle=\frac{1}{\dim V^\lambda_A}\,\delta_{\lambda\mu}\,\delta_{ad}\,\delta_{bc}.\qquad(5.28)$$
--   That is:
--   1. for a single simple module ($\lambda=\mu$) of dimension $n$, the sum equals $\delta_{ad}\delta_{bc}/n$;
--   2. for two non-isomorphic simple modules ($\lambda\neq\mu$), the sum equals $0$.
--
--   The second factor is the plain matrix element of $\rho_\mu(\sigma^*)$, neither conjugated nor transposed. For a group algebra $\mathbb C[G]$, $g^*=g^{-1}/|G|$ and (5.28) is the usual Schur orthogonality of irrep matrix elements; for the commutant algebra $\mathcal A_t$ it yields the expansion $\Omega_{\mathcal A_t}=\sum_\sigma S(\sigma)\otimes S(\sigma^*)^\top$ of the commutant EPR projector (Lemma 5.11).
--
--   Differences from the source:
--   - reading: A a semisimple algebra, tr the trace of its regular representation → A a finite-dimensional semisimple ℂ-algebra, tr(a) the trace of left multiplication by a; reason: the paper's algebras are complex and finite dimensional (commutant algebras, p.34; Lemma 5.11), and the trace of the regular representation is defined only in finite dimension
--   - encoding: a basis B(A) and the dual elements σ* under the trace → a basis (σ_i) indexed by a finite type and any family (σ_i*) with tr(σ_i* σ_j) = δ_ij; reason: the trace form is nondegenerate on a semisimple algebra, so the dual family exists and is unique
--   - encoding: labels λ, µ ∈ Λ(A) of simple modules V^λ_A, V^µ_A with bases, and the factor δ_λµ → two conjuncts: one irreducible matrix representation ρ (λ = µ), and two irreducible representations that are not isomorphic (λ ≠ µ); reason: a simple module with a basis is an irreducible matrix representation; distinct labels are non-isomorphic modules
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Theorem 5.9, Eq. (5.28), p.69, footnote 47

import Mathlib
import Definitions.Def_PathRecording_Supplement_IsIrrepAlg

set_option autoImplicit false

namespace PathRecording.Supplement

/-- Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, Theorem 5.9 (Schur Orthogonality), Eq. (5.28), p.69. Let `A` be a
finite-dimensional semisimple `ℂ`-algebra with a basis `B(A) = {σ_i}`, let `tr` be the trace of the
regular representation of `A`, and let `σ_i*` be the dual elements under this trace,
`tr(σ_i* σ_j) = δ_{ij}`. Then for matrix elements of simple modules in bases,
`Σ_{σ∈B(A)} ⟨a|ρ_λ(σ)|b⟩⟨c|ρ_µ(σ*)|d⟩ = δ_{λµ} δ_{ad} δ_{bc} / dim V^λ_A`:
1. (`λ = µ`) for one irreducible representation `ρ` of dimension `n`, the sum is
   `δ_{ad} δ_{bc} / n`;
2. (`λ ≠ µ`) for two non-isomorphic irreducible representations, the sum is `0`.

**Formalization Note.** `tr(a) = LinearMap.trace ℂ A (LinearMap.mulLeft ℂ a)`, the trace of left
multiplication by `a` on `A` (the regular representation). The second
factor is the plain entry `ρ_µ(σ*)_{cd}`, neither conjugated nor transposed (footnote 47). A simple
module `V^λ_A` with basis `B(V^λ_A)` is an irreducible algebra homomorphism into
`Matrix (Fin n) (Fin n) ℂ` (`IsIrrepAlg`); `λ ≠ µ` means not isomorphic (`AlgRepEquiv`). -/
theorem theorem_5_9 {A : Type*} [Ring A] [Algebra ℂ A] [FiniteDimensional ℂ A] [IsSemisimpleRing A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Module.Basis ι ℂ A) (σd : ι → A)
    (hσd : ∀ i j, LinearMap.trace ℂ A (LinearMap.mulLeft ℂ (σd i * σ j)) = if i = j then 1 else 0) :
    (∀ (n : ℕ) (ρ : A →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ), IsIrrepAlg ρ →
        ∀ a b c d : Fin n,
          ∑ i, ρ (σ i) a b * ρ (σd i) c d = if a = d ∧ b = c then ((n : ℂ))⁻¹ else 0) ∧
    (∀ (m n : ℕ) (ρ : A →ₐ[ℂ] Matrix (Fin m) (Fin m) ℂ) (ρ' : A →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ),
        IsIrrepAlg ρ → IsIrrepAlg ρ' → ¬ AlgRepEquiv ρ ρ' →
        ∀ (a b : Fin m) (c d : Fin n), ∑ i, ρ (σ i) a b * ρ' (σd i) c d = 0) := by sorry

end PathRecording.Supplement
