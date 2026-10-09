-- Prove2me | Theorems.Thm_PhaseCut_Tight_corollary_4_3
-- name    : PhaseCut.Tight.corollary_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:38:59.883186+00:00
-- url     : https://prove2.me/theorems/2dd37d9e-ceaf-4043-a273-ee631ad4ec0d
-- title:
--   Corollary 4.3, p. 13 — for injective A, bᵢ ≠ 0 and |Ax| = b solvable, PhaseCutMod has a unique rank-one solution whenever PhaseLift does
-- statement:
--   Let $A\in\mathbb C^{n\times p}$ be a measurement matrix with rows $a_i^*$ and $b\in\mathbb R^n$ a vector of amplitudes. Assume that
--
--   1. $A$ is injective;
--   2. $b_i\neq 0$ for all $i=1,\dots,n$;
--   3. the phase recovery problem (1) admits an exact solution: there is $x\in\mathbb C^p$ with $|Ax|=b$.
--
--   Consider the two semidefinite relaxations
--
--   $$\text{(PhaseLift)}\quad \min_{X\in\mathbf H_p}\ \operatorname{Tr}(X)\ \ \text{s.t.}\ \ \operatorname{Tr}(a_ia_i^*X)=b_i^2,\ i=1,\dots,n,\ \ X\succeq 0,$$
--
--   $$\text{(PhaseCutMod)}\quad \min_{U\in\mathbf H_n}\ \operatorname{Tr}(BU)\ \ \text{s.t.}\ \ \operatorname{Tr}(MU)=0,\ \ \operatorname{diag}(U)=1,\ \ U\succeq 0,$$
--
--   with $M=\operatorname{diag}(b)(\mathbf I-AA^\dagger)\operatorname{diag}(b)$ and $B=\operatorname{diag}(b)A^{\dagger *}A^\dagger\operatorname{diag}(b)$. If PhaseLift is tight, i.e. has a unique optimal solution and that solution has rank one, then PhaseCutMod is tight as well.
--
--   This is the paper's central noiseless result: the classical MaxCut-type relaxation, refined to PhaseCutMod, recovers the signal whenever PhaseLift does, so the exact-recovery guarantees known for PhaseLift transfer to it.
--
--   **Formalization Note** "Tight" is the corollary's own gloss, "has a unique rank one solution", applied to the optimal set of each program: the set of minimizers is a singleton $\{X\}$ with $\operatorname{Rank}(X)=1$. The gloss on p. 10 for PhaseLift adds "with leading eigenvector $x$"; that describes the known solution and is not part of the corollary's hypothesis, so it is not encoded. Objectives are real parts of traces; $\operatorname{Tr}(a_ia_i^*X)$ is $(AXA^*)_{ii}$; $A^\dagger$ is $(A^*A)^{-1}A^*$, the pseudoinverse under hypothesis 1.
-- source:
--   Waldspurger, d'Aspremont & Mallat, arXiv:1206.0102v3, Corollary 4.3, p. 13

import Mathlib
import Definitions.Def_PhaseCut_Tight_Defs

namespace PhaseCut.Tight

open Matrix
open scoped ComplexOrder

/-- Corollary 4.3, p. 13: if `A` is injective, `bᵢ ≠ 0` for all `i` and (1) has an exact solution,
then PhaseCutMod is tight (its optimal set is a single rank-one matrix) whenever PhaseLift is. -/
theorem corollary_4_3 {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hb : ∀ i, b i ≠ 0) (hsol : IsSolvable A b) :
    IsTight (phaseLiftOptimal A b) → IsTight (phaseCutModOptimal A b) := by sorry

end PhaseCut.Tight
