-- Prove2me | Theorems.Thm_QSVT19_Main_corollary_18
-- name    : QSVT19.Main.corollary_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:57.650293+00:00
-- url     : https://prove2.me/theorems/7021e91d-b716-4212-a384-2f8127f0d3d9
-- title:
--   Corollary 18: singular value transformation by real polynomials
-- statement:
--   Let $U$ be a unitary and $\Pi,\widetilde\Pi$ orthogonal projectors on a finite-dimensional Hilbert space. Let $n\ge1$ and let $P_\Re\in\mathbb R[x]$ be a polynomial of degree $n$ with parity $n\bmod2$ and $|P_\Re(x)|\le1$ for all $x\in[-1,1]$. Then there is $\Phi\in\mathbb R^n$ such that, for every singular value decomposition of $\widetilde\Pi U\Pi$,
--   $$P_\Re^{(SV)}(\widetilde\Pi U\Pi)=\begin{cases}\bigl(\langle+|\otimes\widetilde\Pi\bigr)\bigl(|0\rangle\langle0|\otimes U_\Phi+|1\rangle\langle1|\otimes U_{-\Phi}\bigr)\bigl(|+\rangle\otimes\Pi\bigr)&\text{if $n$ is odd},\\[2pt] \bigl(\langle+|\otimes\Pi\bigr)\bigl(|0\rangle\langle0|\otimes U_\Phi+|1\rangle\langle1|\otimes U_{-\Phi}\bigr)\bigl(|+\rangle\otimes\Pi\bigr)&\text{if $n$ is even.}\end{cases}$$
--   Here $P_\Re^{(SV)}$ is the singular value transformation of Definition 16, $U_\Phi$ the alternating phase modulation sequence (31), and $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$ on one ancilla qubit.
--
--   Every bounded real polynomial of definite parity can thus be applied to the singular values of a block of a unitary, with one ancilla qubit and $n$ uses of $U$ and $U^\dagger$; this is the identity behind the paper's applications.
--
--   **Formalization Note** The hypothesis $n\ge1$ is added: for $n=0$ a constant $P_\Re\equiv c\ne1$ satisfies the conditions, its transformation is $c\Pi$, while the right-hand side is $\Pi$. The ancilla is the first tensor factor; $\Phi$ is chosen before the decomposition.
-- source:
--   Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, p. 19, Corollary 18, (33)

import Definitions.Def_QSVT19_Main_Setting

set_option autoImplicit false

open scoped ComplexOrder
open Polynomial Matrix

namespace QSVT19.Main

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Corollary 18 (Singular value transformation by real polynomials), p. 19: "Let U, Π, Π̃ be
as in Theorem 17. Suppose that P_ℜ ∈ R[x] is a degree-n polynomial satisfying that
• P_ℜ has parity-(n mod 2) and • for all x ∈ [−1, 1]: |P_ℜ(x)| ≤ 1.
Then there exist Φ ∈ R^n, such that
P_ℜ^{(SV)}(Π̃UΠ) = (⟨+| ⊗ Π̃)(|0⟩⟨0| ⊗ U_Φ + |1⟩⟨1| ⊗ U_{−Φ})(|+⟩ ⊗ Π) if n is odd, and
(⟨+| ⊗ Π)(|0⟩⟨0| ⊗ U_Φ + |1⟩⟨1| ⊗ U_{−Φ})(|+⟩ ⊗ Π) if n is even. (33)"

**Formalization Note.** `H_U` is `ι → ℂ` for a finite type `ι`, with inner product
`star v ⬝ᵥ w`; `Π, Π̃` are `Proj, Projt`; "unitary" is `U ∈ Matrix.unitaryGroup ι ℂ` and
"orthogonal projector" is `IsStarProjection` (self-adjoint idempotent). "degree-n" is `natDegree = n`; the parity of `P_ℜ` is that of its image in `ℂ[X]`.
`P_ℜ^{(SV)}(Π̃UΠ)` is Definition 16 applied to `x ↦ P_ℜ(x)` over a singular value decomposition
`S` of `Π̃UΠ` (`svtOdd` for odd `n`, `svtEven` for even `n`); the identity is asserted for every
such decomposition, with `Φ` chosen before it (as `P^{(SV)}` does not depend on the
decomposition). `U_Φ` is `altPhaseSeq`, `⟨+| ⊗ M`, `|+⟩ ⊗ M` and `|0⟩⟨0| ⊗ V + |1⟩⟨1| ⊗ W` are
`plusBra`, `plusKet`, `ctrlSel`, with the ancilla qubit as the first tensor factor. The
hypothesis `1 ≤ n` is added: at `n = 0`, `P_ℜ ≡ c` with `c ≠ 1` satisfies the bullets, its
transformation is `cΠ`, while `Φ ∈ R^0` gives `U_Φ = I` and the right-hand side `Π`. -/
theorem corollary_18 {ι : Type*} [Fintype ι] [DecidableEq ι] (U Proj Projt : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hProj : IsStarProjection Proj) (hProjt : IsStarProjection Projt) (n : ℕ) (hn : 1 ≤ n) (PR : ℝ[X]) (hdeg : PR.natDegree = n) (hpar : QAlgorithms.HasParity (PR.map Complex.ofRealHom) n) (hbd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |PR.eval x| ≤ 1) :
    ∃ Φ : Fin n → ℝ, ∀ S : ProjUnitarySVD U Proj Projt, (Odd n → svtOdd (fun x : ℝ => ((PR.eval x : ℝ) : ℂ)) S = plusBra Projt * ctrlSel (altPhaseSeq U Proj Projt Φ) (altPhaseSeq U Proj Projt (-Φ)) * plusKet Proj) ∧ (Even n → svtEven (fun x : ℝ => ((PR.eval x : ℝ) : ℂ)) S = plusBra Proj * ctrlSel (altPhaseSeq U Proj Projt Φ) (altPhaseSeq U Proj Projt (-Φ)) * plusKet Proj) := by sorry

end QSVT19.Main
