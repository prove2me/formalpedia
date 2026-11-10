-- Prove2me | Theorems.Thm_QThermalClassical_theorem_1_a
-- name    : QThermalClassical.theorem_1_a
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:14:03.290263+00:00
-- url     : https://prove2.me/theorems/05ddd746-e6dc-4450-83a6-b5bbdc8bb134
-- title:
--   Theorem 1(a) — death of entanglement for $(s,k)$-long-range Pauli Hamiltonians, $\beta_{\mathrm{sep}}=\Theta(1/sk)$ (corrected: Θ clause for k ≥ 2)
-- statement:
--   For $(s,k)$-long-range Pauli Hamiltonians (Definition 2.3):
--   1. For every $n$, every $s,k>0$ and every $(s,k)$-long-range Pauli Hamiltonian $H$ on $n$ qubits, the Gibbs state $\rho_\beta(H)$ is separable whenever
--   $$
--   0\le\beta\le\frac1{72sk}\qquad(22).
--   $$
--   2. Conversely, for every even $k\ge2$ and every $s>0$ there exists a commuting $(s,k)$-long-range Pauli Hamiltonian whose Gibbs state is entangled whenever
--   $$
--   \beta>\frac2s\,\mathrm{arctanh}\frac3{k+2}\qquad(23).
--   $$
--   3. $\beta_{\mathrm{sep}}=\Theta(1/sk)$: there are constants $C_1,C_2>0$ such that for every $s>0$ and every integer $k\ge2$,
--   $$
--   \frac{C_1}{sk}\le\beta_{\mathrm{sep}}\le\frac{C_2}{sk}.
--   $$
--
--   This determines the separability threshold of long-range Pauli Hamiltonians up to a constant factor, uniformly in the system size, and shows it is tight even among commuting Hamiltonians.
--
--   Differences from the source:
--   - correction: "$\beta_{\mathrm{sep}}=\Theta(1/sk)$" with no range for $k$ → $\exists\,C_1,C_2>0\ \forall s>0\ \forall k\in\mathbb N,\ k\ge2:\ C_1/(sk)\le\beta_{\mathrm{sep}}\le C_2/(sk)$; reason: false at $k=1$: every $(s,1)$-long-range $H$ is a sum of single-qubit terms, so $e^{-\beta H}$ is a tensor product of positive $2\times2$ matrices and $\rho_\beta(H)\in\mathrm{Sep}_n$ for every $\beta\ge0$; the set in (9) is unbounded, $\beta_{\mathrm{sep}}=+\infty$, and no $C_2/s$ bounds it (e.g. $H=-X_1-X_2$, $s=1$); $k\ge2$ is the range of the converse
--   - encoding: a Pauli Hamiltonian $H=\sum_{a\in A}c_aP_a$ with distinct non-identity Pauli strings → a coefficient function $c$ on Pauli words with $c(I)=0$, $A=\{P: c_P\neq 0\}$; reason: distinctness is automatic and words with coefficient $0$ change neither $H$ nor any condition; no instance changes
--   - encoding: $n$ qubits, $(\mathbb C^2)^{\otimes n}$, $\mathrm{arctanh}$ → qubits `Fin n`, basis `Fin n → Bool`, `Real.artanh`; reason: relabelling; the argument $3/(k+2)\in(0,3/4]$ lies in the domain of arctanh
--   - encoding: $n\ge1$ in (9) → all $n\in\mathbb N$ (in clause 1 and in $\beta_{\mathrm{sep}}$); reason: on $0$ qubits the only Hamiltonian is $0$ and its Gibbs state is the $1\times1$ identity, a product state; nothing changes
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 1(a), eqs. (22)–(23), p.14

import Mathlib
import Definitions.Def_QThermalClassical_ham
import Definitions.Def_QThermalClassical_gibbs
import Definitions.Def_QThermalClassical_IsSeparable
import Definitions.Def_QThermalClassical_IsLongRangePauli
import Definitions.Def_QThermalClassical_IsCommutingPauli
import Definitions.Def_QThermalClassical_betaSep

set_option autoImplicit false

namespace QThermalClassical

/-- **Theorem 1(a) (Death of entanglement, long-range Pauli Hamiltonians).**
1. For every `n`, every `s, k > 0` and every `(s, k)`-long-range Pauli Hamiltonian `H` on
   `n` qubits, the Gibbs state `ρ_β(H)` is separable whenever `0 ≤ β ≤ 1/(72sk)` (22).
2. Conversely, for every even `k ≥ 2` and every `s > 0` there is a commuting
   `(s, k)`-long-range Pauli Hamiltonian whose Gibbs state is entangled whenever
   `β > (2/s) artanh(3/(k + 2))` (23).
3. `β_sep = Θ(1/(sk))`: there are absolute constants `0 < C₁, C₂` with
   `C₁/(sk) ≤ β_sep ≤ C₂/(sk)` for every `s > 0` and every integer `k ≥ 2`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 1(a), eqs. (22)–(23), p.14.

**Formalization Note.** Qubits are `Fin n` with computational basis `Fin n → Bool`;
Hamiltonians are coefficient functions on Pauli words. The `Θ` clause is stated for integers
`k ≥ 2` (correction: at `k = 1` every `(s, 1)`-long-range Hamiltonian has a product Gibbs state
at every `β ≥ 0`, so `β_sep = +∞` there). One witness Hamiltonian serves every `β` above the
threshold. `arctanh` is `Real.artanh`; its argument `3/(k + 2) ≤ 3/4` lies in its domain. -/
theorem theorem_1_a :
    (∀ (n : ℕ) (s k : ℝ), 0 < s → 0 < k → ∀ c : PauliWord (Fin n) → ℝ,
      IsLongRangePauli s k c → ∀ β : ℝ, 0 ≤ β → β ≤ 1 / (72 * s * k) →
        IsSeparable (gibbs (ham c) β)) ∧
    (∀ k : ℕ, 2 ≤ k → Even k → ∀ s : ℝ, 0 < s →
      ∃ (n : ℕ) (c : PauliWord (Fin n) → ℝ), IsLongRangePauli s (k : ℝ) c ∧
        IsCommutingPauli c ∧
        ∀ β : ℝ, 2 / s * Real.artanh (3 / ((k : ℝ) + 2)) < β →
          ¬ IsSeparable (gibbs (ham c) β)) ∧
    (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ s : ℝ, 0 < s → ∀ k : ℕ, 2 ≤ k →
      C₁ / (s * k) ≤ betaSep s (k : ℝ) ∧ betaSep s (k : ℝ) ≤ C₂ / (s * k)) := by sorry

end QThermalClassical
