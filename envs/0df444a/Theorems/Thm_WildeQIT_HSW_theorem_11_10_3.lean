-- Prove2me | Theorems.Thm_WildeQIT_HSW_theorem_11_10_3
-- name    : WildeQIT.HSW.theorem_11_10_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T19:12:25.354067+00:00
-- url     : https://prove2.me/theorems/8fa334d2-42dd-4742-9680-c05776257c88
-- title:
--   Theorem 11.10.3 (AFW inequality): $|H(A|B)_\rho - H(A|B)_\sigma| \le 2\varepsilon\log\dim\mathcal H_A + g_2(\varepsilon)$, with its classical–quantum refinements
-- statement:
--   Let $\rho_{AB},\sigma_{AB}$ be density operators on $\mathcal H_A\otimes\mathcal H_B$ and suppose that
--
--   $$
--   \tfrac12\|\rho_{AB}-\sigma_{AB}\|_1 \le \varepsilon
--   $$
--
--   for some $\varepsilon\in[0,1]$. Write $g_2(\varepsilon) = (\varepsilon+1)\log_2(\varepsilon+1) - \varepsilon\log_2\varepsilon$. Then
--
--   1. $$|H(A|B)_\rho - H(A|B)_\sigma| \le 2\varepsilon\log\dim(\mathcal H_A) + g_2(\varepsilon).$$
--
--   If moreover the states are classical–quantum,
--
--   $$
--   \rho_{XB} = \sum_x p(x)|x\rangle\langle x|_X\otimes\rho^x_B,\qquad \sigma_{XB} = \sum_x q(x)|x\rangle\langle x|_X\otimes\sigma^x_B,
--   $$
--
--   with $p,q$ probability distributions on a finite alphabet $\mathcal X$, $\{|x\rangle\}$ an orthonormal basis of $\mathcal H_X$, and $\rho^x_B,\sigma^x_B$ density operators, and $\tfrac12\|\rho_{XB}-\sigma_{XB}\|_1\le\varepsilon$ with $\varepsilon\in[0,1]$, then
--
--   2. $$|H(X|B)_\rho - H(X|B)_\sigma| \le \varepsilon\log\dim(\mathcal H_X) + g_2(\varepsilon),$$
--   3. $$|H(B|X)_\rho - H(B|X)_\sigma| \le \varepsilon\log\dim(\mathcal H_B) + g_2(\varepsilon).$$
--
--   Clause 2 is the continuity bound used in the converse part of the classical capacity theorem, applied to the shared-randomness states $\Phi_{MM'}$ and $\omega_{MM'}$.
--
--   **Formalization Note** Logarithms are base 2. Finite-dimensional Hilbert spaces are finite index types, $\|\cdot\|_1$ is the published `WildeQIT.traceNorm`, and $\dim\mathcal H_X = |\mathcal X|$. The basis $\{|x\rangle\}$ is given by the columns of a unitary matrix. $H(B|X)$ is the conditional entropy of the operator with its two tensor factors exchanged. This restates the goal of the mission for §11.10 (`08-afw-continuity`), which is not yet published, in this mission's own definitions.
--
--   Differences from the source:
--   - encoding: orthonormal basis {|x⟩} of H_X indexed by the alphabet → columns of a unitary matrix U indexed by the finite type X, with dim H_X = |X|; reason: a family indexed by X is an orthonormal basis exactly when its coordinate matrix is unitary
--   - encoding: H(B|X)ρ = H(BX)ρ − H(X)ρ → qCondEntropy of the operator with its two factors swapped (on B × X); reason: the same entropies of the same operators up to the order of the tensor factors
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.10.3, (11.252)–(11.257), p. 359

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_QMemory_qCondEntropy
import Definitions.Def_WildeQIT_AFW_cqState
import Definitions.Def_WildeQIT_AFW_g2

namespace WildeQIT.HSW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 11.10.3
(AFW Inequality), p. 359: "Let ρ_AB, σ_AB ∈ D(H_A ⊗ H_B). Suppose that ½∥ρ_AB − σ_AB∥₁ ≤ ε,
(11.252) for ε ∈ [0, 1]. Then |H(A|B)_ρ − H(A|B)_σ| ≤ 2ε log dim(H_A) + g₂(ε), (11.253) …
If ρ_XB and σ_XB are classical–quantum and have the following form: ρ_XB = Σ_x p(x)|x⟩⟨x|_X ⊗ ρ^x_B,
σ_XB = Σ_x q(x)|x⟩⟨x|_X ⊗ σ^x_B, where p and q are probability distributions defined over a finite
alphabet 𝒳, {|x⟩} is an orthonormal basis, and ρ^x_B, σ^x_B ∈ D(H_B) for all x ∈ 𝒳, then
|H(X|B)_ρ − H(X|B)_σ| ≤ ε log dim(H_X) + g₂(ε), (11.256)
|H(B|X)_ρ − H(B|X)_σ| ≤ ε log dim(H_B) + g₂(ε). (11.257)"

The first conjunct is (11.253); the second gives (11.256) and (11.257), under the trace-distance
hypothesis (11.252) on the two classical–quantum states.

**Formalization Note.** Finite-dimensional Hilbert spaces are finite index types (`A × B` for
`H_A ⊗ H_B`); `D(H)` is `WildeQIT.IsDensityOperator`; `∥·∥₁` is `WildeQIT.traceNorm`;
`H(A|B)` is `WildeQIT.QMemory.qCondEntropy` (conditioning on the second factor), and `H(B|X)` is the
same quantity for the operator with its two factors swapped. The classical–quantum states are
`WildeQIT.AFW.cqState U p ρx` with the orthonormal basis `{|x⟩}` the columns of a unitary `U`,
and `dim(H_X) = |𝒳|`. Logarithms are base 2, also in `g₂` (`WildeQIT.AFW.g2`). This is a local
restatement of the item drafted in mission `08-afw-continuity` (not yet published). -/
theorem theorem_11_10_3 :
    (∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
        (ρ σ : Matrix (A × B) (A × B) ℂ) (ε : ℝ),
        WildeQIT.IsDensityOperator ρ → WildeQIT.IsDensityOperator σ →
        0 ≤ ε → ε ≤ 1 → WildeQIT.traceNorm (ρ - σ) / 2 ≤ ε →
        |WildeQIT.QMemory.qCondEntropy ρ - WildeQIT.QMemory.qCondEntropy σ| ≤
          2 * ε * Real.logb 2 (Fintype.card A) + WildeQIT.AFW.g2 ε) ∧
    (∀ (X B : Type) [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]
        (U : Matrix X X ℂ) (p q : WildeQIT.FinDist X) (ρx σx : X → Matrix B B ℂ) (ε : ℝ),
        U ∈ Matrix.unitaryGroup X ℂ →
        (∀ x, WildeQIT.IsDensityOperator (ρx x)) → (∀ x, WildeQIT.IsDensityOperator (σx x)) →
        0 ≤ ε → ε ≤ 1 → WildeQIT.traceNorm (WildeQIT.AFW.cqState U p ρx - WildeQIT.AFW.cqState U q σx) / 2 ≤ ε →
        |WildeQIT.QMemory.qCondEntropy (WildeQIT.AFW.cqState U p ρx) - WildeQIT.QMemory.qCondEntropy (WildeQIT.AFW.cqState U q σx)| ≤
            ε * Real.logb 2 (Fintype.card X) + WildeQIT.AFW.g2 ε ∧
          |WildeQIT.QMemory.qCondEntropy ((WildeQIT.AFW.cqState U p ρx).submatrix Prod.swap Prod.swap) -
              WildeQIT.QMemory.qCondEntropy ((WildeQIT.AFW.cqState U q σx).submatrix Prod.swap Prod.swap)| ≤
            ε * Real.logb 2 (Fintype.card B) + WildeQIT.AFW.g2 ε) := by sorry

end WildeQIT.HSW
