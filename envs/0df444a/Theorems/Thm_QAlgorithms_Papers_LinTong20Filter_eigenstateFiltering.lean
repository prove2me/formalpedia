-- Prove2me | Theorems.Thm_QAlgorithms_Papers_LinTong20Filter_eigenstateFiltering
-- name    : QAlgorithms.Papers.LinTong20Filter.eigenstateFiltering
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:04:55.667695+00:00
-- url     : https://prove2.me/theorems/321df5e5-acaf-40d3-ae33-ce6c83cda433
-- title:
--   Lin–Tong Theorem 3: eigenstate filtering block-encodes the spectral projector with O((α/Δ) log(1/ε)) queries
-- statement:
--   This is the eigenstate filtering theorem of Lin and Tong.
--
--   An $(m+n)$-qubit unitary $U$ is an $(\alpha,m,\varepsilon)$-block-encoding of an $n$-qubit operator $A$ if
--   $$\bigl\|A-\alpha\,(\langle 0^m|\otimes I)\,U\,(|0^m\rangle\otimes I)\bigr\|\le\varepsilon,$$
--   where $\|\cdot\|$ is the operator norm and the $m$ ancilla qubits form the first register. For a Hermitian $n$-qubit matrix $H$ and a real number $\lambda$, let $P_\lambda$ be the orthogonal projector onto the $\lambda$-eigenspace of $H$ (which may be degenerate).
--
--   There are absolute constants $C>0$ and $\varepsilon_0\in(0,1)$ such that the following holds. For all $n,m\in\mathbb N$ and all reals $\alpha>0$, $\Delta>0$, $\lambda$ and $\varepsilon\in(0,\varepsilon_0]$, there is a quantum circuit $\mathcal C$ on $m+2+n$ qubits, built from two-qubit gates and black-box applications (possibly controlled, possibly inverted) of an $(m+n)$-qubit unitary $U_H$, which uses
--   $$\#\text{queries}\le C\,\frac{\alpha}{\Delta}\log\frac1\varepsilon,\qquad \#\text{other gates}\le C\,(m+1)\,\frac{\alpha}{\Delta}\log\frac1\varepsilon,$$
--   and such that for every Hermitian $H$ and every $(\alpha,m,0)$-block-encoding $U_H$ of $H$ for which $\lambda$ is an eigenvalue of $H$ with every other eigenvalue $\mu$ satisfying $|\mu-\lambda|\ge\Delta$, the unitary $\mathcal C[U_H]$ is a $(1,m+2,\varepsilon)$-block-encoding of $P_\lambda$.
--
--   Applied to an initial state with overlap $\gamma$ with the $\lambda$-eigenspace, this prepares the target eigenstate with logarithmic dependence on the precision; the paper uses it to solve the quantum linear systems problem with near-optimal query complexity.
--
--   **Formalization Note** The circuit depends only on the known data $n,m,\alpha,\Delta,\lambda,\varepsilon$, not on $H$ or $U_H$. Primitive gates are taken to be arbitrary two-qubit unitaries (the source does not fix a gate set and assumes exact phase factors). The printed gate bound $O((m\alpha/\Delta)\log(1/\varepsilon))$ is stated with $m+1$ in place of $m$: at $m=0$ the printed bound would force zero gates, while the source's own Theorem 1' gives $O((m+1)\ell)$ gates.
-- source:
--   Optimal polynomial based quantum eigenstate filtering with application to solving quantum linear systems (Lin, Tong), arXiv:1910.14596v4, Theorem 3, PDF p. 8. https://arxiv.org/abs/1910.14596v4 . PDF SHA-256: 88cd658770f06e2cf3dcd62314e1cd074c42794d202d67918a52569848333f60.

import Definitions.Def_QAlgorithms_Defs_SpectralFilter
set_option autoImplicit false

namespace QAlgorithms.Papers.LinTong20Filter

open QAlgorithms

/-- **LT Theorem 3** (PDF p.8), eigenstate filtering.

Let `H` be a Hermitian matrix and `U_H` an `(α, m, 0)`-block-encoding of `H`. If `λ` is an
eigenvalue of `H` separated from the rest of the spectrum by a gap `Δ`, then one can construct a
`(1, m + 2, ε)`-block-encoding of the spectral projector `P_λ` (onto the `λ`-eigenspace, possibly
degenerate) using `O((α/Δ) log(1/ε))` applications of (controlled-) `U_H` and `U_H†` and
`O((mα/Δ) log(1/ε))` other primitive quantum gates.

Encoding choices.
* The circuit is chosen from the known data `n, m, α, Δ, λ, ε` only, before `H` and `U_H`
  (trap Q2; §3, p.7: "a known eigenvalue λ"); `U_H` enters only as the oracle of an
  `OracleCircuit`, whose `queryCount` counts every application (plain or controlled, `U_H` or
  `U_H†`; trap Q6).
* The circuit acts on exactly `m + 2 + n` wires, ancillas first: the `m + 2` ancillas of the
  produced encoding and the `n` system qubits, no further workspace.
* "Primitive quantum gates" is not fixed by the source; the frozen `twoQubitGateSet` (all
  two-qubit unitaries) is used: the construction needs arbitrary-angle rotations (p.6: phase
  factors "given and computed without error").
* `O(·)` constants: one absolute `C > 0` and one absolute threshold `ε₀ ∈ (0, 1)`, quantified
  before everything (trap 8); the bound is an `ε → 0` statement (as `ε → 1`, `log(1/ε) → 0`).
* The gap: `λ` is an eigenvalue of `H` and every eigenvalue `μ ≠ λ` has `|μ − λ| ≥ Δ`
  (frozen `IsGapSeparatedEigenvalue`); `Δ > 0`, and `α > 0` (Appendix A, p.26).

**Correction** (trap 30). Printed: `O((mα/Δ) log(1/ε))` other gates. Changed: `(m + 1)` in place
of `m`. Why: at `m = 0` the printed bound forces zero gates, while the source's own Theorem 1'
(p.6), on which the proof rests, gives `O((m + 1)ℓ)` gates. -/
theorem eigenstateFiltering :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧
      ∀ (n m : ℕ) (α Δ lam ε : ℝ), 0 < α → 0 < Δ → 0 < ε → ε ≤ ε₀ →
        ∃ c : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => m + n) (m + 2 + n),
          (c.queryCount 0 : ℝ) ≤ C * (α / Δ) * Real.log (1 / ε) ∧
          (c.gateCount : ℝ) ≤ C * ((m : ℝ) + 1) * (α / Δ) * Real.log (1 / ε) ∧
          ∀ (H : Matrix (Qubits n) (Qubits n) ℂ) (UH : Matrix (Qubits (m + n)) (Qubits (m + n)) ℂ),
            H.IsHermitian → IsQubitBlockEncoding m n UH α 0 H →
            IsGapSeparatedEigenvalue H lam Δ →
            IsQubitBlockEncoding (m + 2) n (c.unitary fun _ => UH) 1 ε
              (spectralProjector H lam) := by
  sorry




end QAlgorithms.Papers.LinTong20Filter
