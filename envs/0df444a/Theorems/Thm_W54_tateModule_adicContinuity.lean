-- Prove2me | Theorems.Thm_W54_tateModule_adicContinuity
-- name    : W54.tateModule_adicContinuity
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/5ab2bc22-d95e-5f53-919d-8fd539b38d9a
-- title:
--   Finite-level Galois triviality transfers to the p-adic Tate module
-- statement:
--   Fix natural numbers $M$ and $p$ with $M$ nonzero, and give $J_0(M) :=$ `JZero M`, the degree-zero divisor class group $\mathrm{Pic}^0$ of the base-changed modular function field `modularFunctionFieldBar M` over $\overline{\mathbb{Q}}$ (degree-zero divisors modulo principal ones), its `heckeModuleBar M` module structure over $\mathbb{T} :=$ `HeckeAlg` $= \mathbb{Z}[T_\ell : \ell \text{ prime}]$ (given by the Hecke operators when these commute, and by the specialisation sending all $T_\ell$ to $0$ otherwise). Assume the hypothesis: for every $n$ there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ fixing $L$ pointwise fixes every $v \in J_0(M)$ killed by $p^n$ (i.e. $v$ in the $\mathbb{Z}$-torsion submodule `Pic0.torsion` at $p^n$). The conclusion is that for every $n$ there is likewise a finite-dimensional intermediate field $L$ such that for every $\sigma$ fixing $L$ pointwise and every $x$ in [`TateModule p (JZero M)`](def/EllipticCurve_TateModule.html#L15) — the $\mathbb{T}$-submodule of sequences $x : \mathbb{N} \to J_0(M)$ with $x(0) = 0$ and $p \cdot x(n+1) = x(n)$ — there exists $y$ in that same submodule with $p^n \cdot y = (m \mapsto \sigma \cdot x(m)) - x$.
--
--   This is the finite-level, or continuity, statement for the Galois action on the $p$-adic Tate module of the Jacobian $J_0(M)$: triviality of the action on $p^n$-torsion over a number field implies that $\sigma x - x$ is divisible by $p^n$ inside the Tate module. It feeds the construction and local analysis of the $p$-adic Galois representations attached to newforms, being used in the statements about adic representations, reduction kernels, monodromy spans and eigenplanes in the Tate module of $J_0(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_W54_tateModule_adicContinuity.lean

import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_ModularCurve_AttachmentConcrete
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem W54.tateModule_adicContinuity (M p : ℕ) [NeZero M] :
    letI := ModularCurve.heckeModuleBar M
    ∀ (_h : ∀ n : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ L ∧
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
          ∀ v : JZero M,
            v ∈ Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar M) (p ^ n) →
            σ • v = v),
    ∀ n : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ L ∧
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
          ∀ x ∈ TateModule p (JZero M), ∃ y ∈ TateModule p (JZero M),
            (p ^ n : ℕ) • y = (fun m => σ • x m) - x := by sorry
