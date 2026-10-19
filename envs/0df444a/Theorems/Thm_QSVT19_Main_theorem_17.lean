-- Prove2me | Theorems.Thm_QSVT19_Main_theorem_17
-- name    : QSVT19.Main.theorem_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:40.012691+00:00
-- url     : https://prove2.me/theorems/3d8d7bd0-f62e-4bdd-8893-be1cf1c7bf07
-- title:
--   Theorem 17: singular value transformation by alternating phase modulation
-- statement:
--   Let $U$ be a unitary and $\Pi,\widetilde\Pi$ orthogonal projectors on a finite-dimensional Hilbert space. Let $n\in\mathbb N$, $\Phi\in\mathbb R^n$ and $P\in\mathbb C[x]$ be such that, for every $x\in[-1,1]$, $P(x)$ is the top-left entry of $\prod_{j=1}^n\bigl(e^{i\varphi_j\sigma_z}R(x)\bigr)$ (equation (14)). Then, for every singular value decomposition of $\widetilde\Pi U\Pi$,
--   $$P^{(SV)}(\widetilde\Pi U\Pi)=\begin{cases}\widetilde\Pi\,U_\Phi\,\Pi&\text{if $n$ is odd},\\ \Pi\,U_\Phi\,\Pi&\text{if $n$ is even},\end{cases}$$
--   where $P^{(SV)}$ is the odd, respectively even, singular value transformation of Definition 16 and $U_\Phi$ is the alternating phase modulation sequence (31).
--
--   This is the paper's central identity: a sequence of $n$ uses of $U$ and $U^\dagger$ interleaved with phase rotations applies the polynomial $P$ to every singular value of the block $\widetilde\Pi U\Pi$.
--
--   **Formalization Note** "$P$ and $\Phi$ as in Corollary 8" is read as (14), the only property the proof uses; Corollary 8's conditions on $P$ are not assumed. No bound on $n$ is needed.
-- source:
--   Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, p. 18, Theorem 17, (32)

import Definitions.Def_QSVT19_Main_Setting

set_option autoImplicit false

open scoped ComplexOrder
open Polynomial Matrix

namespace QSVT19.Main

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Theorem 17, p. 18: "Let H_U be a finite-dimensional Hilbert space and let U, Π, Π̃ ∈
End(H_U) be linear operators on H_U such that U is a unitary, and Π, Π̃ are orthogonal projectors.
Let P ∈ C[x] and Φ ∈ R^n is as in Corollary 8, then
P^{(SV)}(Π̃UΠ) = Π̃U_ΦΠ if n is odd, and ΠU_ΦΠ if n is even. (32)"

**Formalization Note.** `H_U` is `ι → ℂ` for a finite type `ι`, with inner product
`star v ⬝ᵥ w`; `Π, Π̃` are `Proj, Projt`; "unitary" is `U ∈ Matrix.unitaryGroup ι ℂ` and
"orthogonal projector" is `IsStarProjection` (self-adjoint idempotent). "P and Φ as in Corollary 8" is read as (14): the top-left entry of
`∏_{j=1}^n e^{iφ_jσ_z}R(x)` is `P(x)` for every `x ∈ [−1, 1]`. That is the only property of `P`
and `Φ` the proof uses; Corollary 8's bullets on `P` are not assumed. `P^{(SV)}` is Definition
16 over an arbitrary singular value decomposition `S` of `Π̃UΠ` (`svtOdd` for odd `n`,
`svtEven` for even `n`, as in (32)); `U_Φ` is `altPhaseSeq` (Definition 15). No bound on `n` is
needed: at `n = 0`, (14) forces `P = 1` and both sides are `Π`. -/
theorem theorem_17 {ι : Type*} [Fintype ι] [DecidableEq ι] (U Proj Projt : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hProj : IsStarProjection Proj) (hProjt : IsStarProjection Projt) (n : ℕ) (Φ : Fin n → ℝ) (P : ℂ[X]) (hΦ : ∀ x ∈ Set.Icc (-1 : ℝ) 1, qspRefl Φ x 0 0 = P.eval (x : ℂ)) (S : ProjUnitarySVD U Proj Projt) :
    (Odd n → svtOdd (fun x => P.eval (x : ℂ)) S = Projt * altPhaseSeq U Proj Projt Φ * Proj) ∧ (Even n → svtEven (fun x => P.eval (x : ℂ)) S = Proj * altPhaseSeq U Proj Projt Φ * Proj) := by sorry

end QSVT19.Main
