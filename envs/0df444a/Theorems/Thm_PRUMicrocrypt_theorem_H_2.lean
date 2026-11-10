-- Prove2me | Theorems.Thm_PRUMicrocrypt_theorem_H_2
-- name    : PRUMicrocrypt.theorem_H_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:29:57.725897+00:00
-- url     : https://prove2.me/theorems/5bbd24e1-0569-4a04-9e1e-7bbf5ee4b50e
-- title:
--   Theorem H.2 — direct controlled Haar comparison: $\tfrac12\|\mathbb E_U\rho^U_t-\mathrm{Tr}_{LR}|v_t\rangle\langle v_t|\|_1\le 9t(t+1)N^{-1/8}$
-- statement:
--   Let $N=2^n$ and $0\le t<N$. Consider an algorithm making $t$ queries in the model of Section 3: a unit initial vector $|\psi_0\rangle$ on selector, query register and an arbitrary finite reference, and inter-query operations $A_1,\dots,A_t$. Let $\rho^U_t=|\psi_t(U)\rangle\langle\psi_t(U)|$ be its state after $t$ queries to $\mathrm{Select}(U)$. Let $|v_t\rangle$ be its global state after $t$ queries to the controlled path-recording oracle $\widehat V$, starting from empty relations as in (3.18). Then
--
--   $$\frac12\Big\|\mathbb E_{U\leftarrow\mathrm{Haar}(U(N))}[\rho^U_t]-\mathrm{Tr}_{LR}|v_t\rangle\langle v_t|\Big\|_1\le 9t(t+1)N^{-1/8}.$$
--
--   The path-recording oracle thus simulates adaptive, coherently controlled access to a Haar-random unitary and all four of its interfaces. This is the Haar side of Theorem 4.1.
--
--   Differences from the source:
--   - encoding: inter-query isometries and selector projections P_0, …, P_4 with ∑ P_a = I → unitaries on a fixed finite space ℂ⁵ ⊗ ℂᴺ ⊗ ℂ^W and P_a = |a⟩⟨a|; reason: every finite-dimensional isometric algorithm and selector embed into this model with the same reduced states
--   - encoding: E_{U←Haar}[ρ^U_t], ℋ_LR, ‖·‖_1 → entrywise integral against the published unitaryHaar (2 ^ n), the record basis, the published traceNorm; reason: the same quantities
-- source:
--   Gulati–Khurana–Tomer, How to Build Pseudorandom Unitaries in Microcrypt, arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), Theorem H.2, p.82 (model (3.17)–(3.18), p.23)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_PRUMicrocrypt_recorderHat

set_option autoImplicit false

namespace PRUMicrocrypt

open MeasureTheory

/-- **Theorem H.2 (Direct controlled Haar comparison).** "Let 0 ≤ t < N and consider an algorithm
making t unitary-oracle queries. Let |𝒜^V_t⟩_ABLR := |v_t⟩ be its global state after t queries to the
controlled path-recording oracle V̂, starting with empty relations as in (3.18). Then
(1/2)‖E_{U←Haar}[ρ^U_t] − Tr_LR|v_t⟩⟨v_t|‖_1 ≤ 9t(t + 1)N^{−1/8}. (H.4)"
A. Gulati, D. Khurana, K. Tomer, *How to Build Pseudorandom Unitaries in Microcrypt*,
arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), Theorem H.2, p.82 (model (3.17)–(3.18), p.23).

**Formalization Note.** `N = 2ⁿ`. The algorithm is a `QueryAlg` (unit initial vector on selector ⊗
query ⊗ arbitrary finite reference, unitary inter-query operations on that space). `ρ^U_t` is
`alg.rho U t` with `U` Haar on `U(N)` (the published `unitaryHaar (2 ^ n)`); its expectation is
taken entrywise. `|v_t⟩` is `alg.recorderState t`; `‖·‖₁` is the published `traceNorm`. -/
theorem theorem_H_2 (n t : ℕ) (ht : t < 2 ^ n) {W : Type*} [Fintype W] [DecidableEq W]
    (alg : QueryAlg n t W) :
    (1 / 2 : ℝ) * QAlgorithms.traceNorm
        (Matrix.of (fun i j => ∫ V, alg.rho (V : Matrix (Idx n) (Idx n) ℂ) t i j
            ∂ QAlgorithms.Schur.unitaryHaar (2 ^ n)) - partialTraceLR (alg.recorderState t)) ≤
      9 * (t : ℝ) * ((t : ℝ) + 1) * ((2 : ℝ) ^ n) ^ (-(1 / 8 : ℝ)) := by sorry

end PRUMicrocrypt
