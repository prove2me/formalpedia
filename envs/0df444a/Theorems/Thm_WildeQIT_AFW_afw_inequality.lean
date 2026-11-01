-- Prove2me | Theorems.Thm_WildeQIT_AFW_afw_inequality
-- name    : WildeQIT.AFW.afw_inequality
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:36:58.960376+00:00
-- url     : https://prove2.me/theorems/110276ef-29d9-40d4-99fb-5f60c8749849
-- title:
--   Theorem 11.10.3 (AFW inequality): $|H(A|B)_\rho - H(A|B)_\sigma| \le 2\varepsilon\log\dim\mathcal H_A + g_2(\varepsilon)$, and $\varepsilon\log\dim + g_2(\varepsilon)$ on classical–quantum states
-- statement:
--   Write $H(A|B)_\rho = H(AB)_\rho - H(B)_\rho$ for the conditional quantum entropy (base-2 logarithms), $\|\cdot\|_1$ for the trace norm, and
--
--   $$
--   g_2(\varepsilon) \equiv (\varepsilon+1)\log_2(\varepsilon+1) - \varepsilon\log_2\varepsilon .
--   $$
--
--   1. **General states.** Let $\rho_{AB},\sigma_{AB}$ be density operators on $\mathcal H_A\otimes\mathcal H_B$ and $\varepsilon\in[0,1]$ with $\tfrac12\|\rho_{AB}-\sigma_{AB}\|_1 \le \varepsilon$. Then
--   $$
--   |H(A|B)_\rho - H(A|B)_\sigma| \le 2\varepsilon\log\dim(\mathcal H_A) + g_2(\varepsilon) .
--   $$
--   2. **Classical–quantum states.** Let $\mathcal X$ be a finite alphabet, $\{|x\rangle\}$ an orthonormal basis of $\mathcal H_X$, $p$ and $q$ probability distributions on $\mathcal X$, and $\rho^x_B,\sigma^x_B$ density operators on $\mathcal H_B$ for all $x$. Put
--   $$
--   \rho_{XB} = \sum_x p(x)\,|x\rangle\langle x|_X\otimes\rho^x_B, \qquad \sigma_{XB} = \sum_x q(x)\,|x\rangle\langle x|_X\otimes\sigma^x_B ,
--   $$
--   and let $\varepsilon\in[0,1]$ with $\tfrac12\|\rho_{XB}-\sigma_{XB}\|_1 \le \varepsilon$. Then
--   $$
--   |H(X|B)_\rho - H(X|B)_\sigma| \le \varepsilon\log\dim(\mathcal H_X) + g_2(\varepsilon),
--   $$
--   $$
--   |H(B|X)_\rho - H(B|X)_\sigma| \le \varepsilon\log\dim(\mathcal H_B) + g_2(\varepsilon).
--   $$
--
--   The bound depends only on the dimension of the system whose entropy is conditioned, not on the conditioning system, which is what makes it usable for converse theorems where the conditioning system is a large output of many channel uses. On classical–quantum states the factor $2$ drops, in both directions of conditioning.
--
--   **Formalization Note** Hilbert spaces are finite index types (`A × B` for $\mathcal H_A\otimes\mathcal H_B$, Kronecker convention). Density operators are `WildeQIT.IsDensityOperator`, the trace norm is `WildeQIT.traceNorm`, $H(A|B)$ is the published `AlickiFannes.condEntropy` (von Neumann entropy `QAlgorithms.vnEntropy`, base 2, tracing out the first factor), and $g_2$ is `WildeQIT.AFW.g2`. The classical–quantum states are `WildeQIT.AFW.cqState`. The two parts are stated as one conjunction, each part quantified over its own finite types.
--
--   Differences from the source:
--   - encoding: the orthonormal basis $\{|x\rangle\}$ of $\mathcal H_X$ indexed by $\mathcal X$ → the columns of a unitary matrix $U$ indexed by the finite type `X`, with $\dim\mathcal H_X = |\mathcal X|$; reason: a family indexed by $\mathcal X$ is an orthonormal basis exactly when the matrix of its coordinates is unitary.
--   - encoding: $H(B|X)_\rho = H(BX)_\rho - H(X)_\rho$ → `AlickiFannes.condEntropy` of the operator with its two factors swapped (on `B × X`); reason: the same entropies, of the same operators up to the order of the tensor factors.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.10.3, (11.252)–(11.257), p. 359

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_AlickiFannes_condEntropy
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_AFW_g2
import Definitions.Def_WildeQIT_AFW_cqState

namespace WildeQIT.AFW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 11.10.3
(AFW Inequality), p. 359: "Let ρ_AB, σ_AB ∈ D(H_A ⊗ H_B). Suppose that ½∥ρ_AB − σ_AB∥₁ ≤ ε,
(11.252) for ε ∈ [0, 1]. Then |H(A|B)_ρ − H(A|B)_σ| ≤ 2ε log dim(H_A) + g₂(ε), (11.253) …
If ρ_XB and σ_XB are classical–quantum and have the following form: ρ_XB = Σ_x p(x)|x⟩⟨x|_X ⊗ ρ^x_B,
σ_XB = Σ_x q(x)|x⟩⟨x|_X ⊗ σ^x_B, where p and q are probability distributions defined over a finite
alphabet 𝒳, {|x⟩} is an orthonormal basis, and ρ^x_B, σ^x_B ∈ D(H_B) for all x ∈ 𝒳, then
|H(X|B)_ρ − H(X|B)_σ| ≤ ε log dim(H_X) + g₂(ε), (11.256)
|H(B|X)_ρ − H(B|X)_σ| ≤ ε log dim(H_B) + g₂(ε). (11.257)"

The first conjunct is (11.253); the second gives (11.256) and (11.257).

**Formalization Note.** Finite-dimensional Hilbert spaces are finite index types (`A × B` for
`H_A ⊗ H_B`, Kronecker convention); `D(H)` is `WildeQIT.IsDensityOperator`; `∥·∥₁` is
`WildeQIT.traceNorm`. `H(A|B)_ρ = H(AB)_ρ − H(B)_ρ` (Definition 11.4.1) is the published
`AlickiFannes.condEntropy`, which traces out the **first** factor; `H(B|X)` is the same quantity
for the operator with its two factors swapped (`submatrix Prod.swap Prod.swap`, on `B × X`).
Entropies use `log₂` (`QAlgorithms.vnEntropy`), as do `log dim` and `g₂` (`WildeQIT.AFW.g2`).
The classical–quantum states are `WildeQIT.AFW.cqState U p ρx`, with the orthonormal basis
`{|x⟩}` the columns of a unitary `U`, and `dim(H_X) = |𝒳|`. -/
theorem afw_inequality :
    (∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
        (ρ σ : Matrix (A × B) (A × B) ℂ) (ε : ℝ),
        WildeQIT.IsDensityOperator ρ → WildeQIT.IsDensityOperator σ →
        0 ≤ ε → ε ≤ 1 → WildeQIT.traceNorm (ρ - σ) / 2 ≤ ε →
        |AlickiFannes.condEntropy ρ - AlickiFannes.condEntropy σ| ≤
          2 * ε * Real.logb 2 (Fintype.card A) + g2 ε) ∧
    (∀ (X B : Type) [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]
        (U : Matrix X X ℂ) (p q : WildeQIT.FinDist X) (ρx σx : X → Matrix B B ℂ) (ε : ℝ),
        U ∈ Matrix.unitaryGroup X ℂ →
        (∀ x, WildeQIT.IsDensityOperator (ρx x)) → (∀ x, WildeQIT.IsDensityOperator (σx x)) →
        0 ≤ ε → ε ≤ 1 → WildeQIT.traceNorm (cqState U p ρx - cqState U q σx) / 2 ≤ ε →
        |AlickiFannes.condEntropy (cqState U p ρx) - AlickiFannes.condEntropy (cqState U q σx)| ≤
            ε * Real.logb 2 (Fintype.card X) + g2 ε ∧
          |AlickiFannes.condEntropy ((cqState U p ρx).submatrix Prod.swap Prod.swap) -
              AlickiFannes.condEntropy ((cqState U q σx).submatrix Prod.swap Prod.swap)| ≤
            ε * Real.logb 2 (Fintype.card B) + g2 ε) := by sorry

end WildeQIT.AFW
