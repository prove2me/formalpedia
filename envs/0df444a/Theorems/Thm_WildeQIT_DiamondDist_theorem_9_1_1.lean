-- Prove2me | Theorems.Thm_WildeQIT_DiamondDist_theorem_9_1_1
-- name    : WildeQIT.DiamondDist.theorem_9_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:04.389612+00:00
-- url     : https://prove2.me/theorems/a70bcc8a-eed5-442d-abd1-c7660b6797ea
-- title:
--   Theorem 9.1.1: $\|\mathcal N-\mathcal M\|_\diamond$ is attained on a pure state $|\psi\rangle_{RA}$ with $\dim\mathcal H_R=\dim\mathcal H_A$
-- statement:
--   Let $\mathcal N,\mathcal M:\mathcal L(\mathcal H_A)\to\mathcal L(\mathcal H_B)$ be quantum channels between finite-dimensional systems, $\dim\mathcal H_A\ge1$. Their **diamond-norm distance** (Definition 9.1.3) is
--
--   $$
--   \|\mathcal N-\mathcal M\|_\diamond=\sup_{n}\ \sup_{\rho_{R_nA}\in\mathcal D(\mathcal H_{R_n}\otimes\mathcal H_A)}\bigl\|(\mathrm{id}_{R_n}\otimes\mathcal N)(\rho_{R_nA})-(\mathrm{id}_{R_n}\otimes\mathcal M)(\rho_{R_nA})\bigr\|_1 ,
--   $$
--
--   the supremum over all reference systems $R_n$ of every dimension $n$ and all (mixed) states of $R_nA$. Then
--
--   $$
--   \|\mathcal N-\mathcal M\|_\diamond=\max_{|\psi\rangle_{RA}}\bigl\|(\mathrm{id}_R\otimes\mathcal N)(|\psi\rangle\langle\psi|_{RA})-(\mathrm{id}_R\otimes\mathcal M)(|\psi\rangle\langle\psi|_{RA})\bigr\|_1 ,
--   $$
--
--   where the maximum is over all unit vectors $|\psi\rangle_{RA}\in\mathcal H_R\otimes\mathcal H_A$, $\||\psi\rangle_{RA}\|_2=1$, with $\dim\mathcal H_R=\dim\mathcal H_A$. In particular the maximum is attained, and its value equals the supremum over all references and mixed inputs.
--
--   The theorem shows that the channel distinguishability measure needs neither mixed inputs nor a reference larger than the input, and it is what allows (9.78) to be taken as the definition of the diamond-norm distance in the capacity chapters.
--
--   **Formalization Note** Channels are in Kraus form (`WildeQIT.QChannel`, every channel has one by Theorem 4.4.1) and $\mathrm{id}_R\otimes\mathcal N$ is `QChannel.tensorIdApply`. The diamond norm is the published `WildeQIT.diamondNorm`: a real `sSup` over references `Fin n` and density operators, with the unnormalized trace distance; that set is bounded by $2$, so the `sSup` is the book's supremum. The reference $R$ of the conclusion is indexed by a copy of the input index type `a`, $\psi:a\times a\to\mathbb C$ with $\sum_i|\psi_i|^2=1$, and $|\psi\rangle\langle\psi|$ is `vecMulVec ψ (star ψ)`. The maximum is `IsGreatest`: the diamond-norm value is attained by some unit vector and bounds every unit vector's value.
--
--   Differences from the source:
--   - encoding: $\max_{|\psi\rangle_{RA}}$ → `IsGreatest` of the set of values over unit vectors $\psi$ on $a\times a$; reason: states that the maximum exists and equals $\|\mathcal N-\mathcal M\|_\diamond$
--   - encoding: $\mathcal H_R$ with $\dim\mathcal H_R=\dim\mathcal H_A$ → reference indexed by the input index type `a`; reason: any Hilbert space of that dimension is isometric to this one, and the trace norm is invariant under that isometry
--   - encoding: $\mathcal H_A$ a Hilbert space → `[Nonempty a]`; reason: excludes the zero-dimensional space, where no unit vector exists and no state is defined
--   - encoding: quantum channels → Kraus families `WildeQIT.QChannel a b`; reason: every channel has a Kraus representation (Theorem 4.4.1), and every Kraus family is a channel
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 9.1.1, p. 261, eq. (9.78), with Definition 9.1.3, eq. (9.77)

import Definitions.Def_WildeQIT_diamondNorm

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 9.1.1, p. 261.
-/

open Matrix

namespace WildeQIT.DiamondDist

/-- **Theorem 9.1.1** (Wilde, arXiv:1106.1445v8, p. 261, eq. (9.78)). Let
`N, M : L(H_A) → L(H_B)` be quantum channels. Then
`‖N − M‖◇ = max_{|ψ⟩_RA} ‖(id_R ⊗ N)(|ψ⟩⟨ψ|_RA) − (id_R ⊗ M)(|ψ⟩⟨ψ|_RA)‖₁`, where the
optimization is over all `|ψ⟩_RA ∈ H_R ⊗ H_A` with `‖|ψ⟩_RA‖₂ = 1` and `dim(H_R) = dim(H_A)`.

Formalization Note: `‖N − M‖◇` is the published `WildeQIT.diamondNorm` (Definition 9.1.3, the
supremum over all `Fin n` references and all density operators on `R_n ⊗ A`). The reference
`R` with `dim(H_R) = dim(H_A)` is indexed by a copy of `a`; `ψ : a × a → ℂ` is a unit vector and
`|ψ⟩⟨ψ|` is `vecMulVec ψ (star ψ)`. The maximum is stated as `IsGreatest` (attained, and an
upper bound). `[Nonempty a]`: `H_A` is a Hilbert space of positive dimension. -/
theorem theorem_9_1_1 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Nonempty a] (N M : QChannel a b) :
    IsGreatest {x : ℝ | ∃ ψ : a × a → ℂ, ∑ i, ‖ψ i‖ ^ 2 = 1 ∧ x = traceDist (N.tensorIdApply a (vecMulVec ψ (star ψ))) (M.tensorIdApply a (vecMulVec ψ (star ψ)))} (diamondNorm N M) := by sorry

end WildeQIT.DiamondDist
