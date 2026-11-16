-- Prove2me | Theorems.Thm_QThermalClassical_Supplement_theorem_1_b
-- name    : QThermalClassical.Supplement.theorem_1_b
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:39:38.919649+00:00
-- url     : https://prove2.me/theorems/3b5679ef-1ea4-429b-b034-03b172123104
-- title:
--   Theorem 1(b) (corrected: converse and $\Theta$ clause for $k\ge3$) — low-intersection Gibbs states separable for $\beta\le1/(96\mathfrak d)$, entangled above $96\log2/(\mathfrak d+2)$
-- statement:
--   Let $\mathfrak d,k>0$ be real. For $(\mathfrak d,k)$-low-intersection Pauli Hamiltonians the death-of-entanglement temperature is $\Theta(1/\mathfrak d)$:
--
--   1. For every $n$ and every $(\mathfrak d,k)$-low-intersection Pauli Hamiltonian $H$ on $n$ qubits, the Gibbs state $\rho_\beta(H)$ is separable ($\in\mathrm{Sep}_n$) whenever
--   $$
--   0\le\beta\le\frac1{96\,\mathfrak d}.
--   $$
--   2. Conversely, there is a sequence $H_j$ of commuting $3$-local Pauli Hamiltonians, each $(\mathfrak d_j,3)$-low-intersection with $\mathfrak d_j$ its dual degree and $\mathfrak d_j\to\infty$, such that $\rho_\beta(H_j)$ is entangled for all
--   $$
--   \beta>\frac{96\log 2}{\mathfrak d_j+2}.
--   $$
--   3. There are constants $C_1,C_2>0$ and $\mathfrak d_0$ such that for every real $\mathfrak d\ge\mathfrak d_0$ and every integer $k\ge3$,
--   $$
--   \frac{C_1}{\mathfrak d}\le\beta_{\mathrm{sep}}(\mathcal F_{\mathfrak d,k})\le\frac{C_2}{\mathfrak d}.
--   $$
--
--   The separability bound improves the $\Omega(1/\mathfrak d k)$ of [BLMT24] by a factor $k$, and the converse shows it is tight up to constants.
--
--   Differences from the source:
--   - correction: the converse and $\beta_{\mathrm{sep}}=\Theta(1/\mathfrak d)$ for $(\mathfrak d,k)$-low-intersection Hamiltonians, with no range for $k$ → converse for $3$-local Hamiltonians; $\Theta$ clause for integers $k\ge3$; reason: false at $k=1$: a $1$-local $H$ is a sum of single-qubit terms, $e^{-\beta H}$ is a tensor product of positive $2\times2$ matrices and $\rho_\beta(H)\in\mathrm{Sep}_n$ for every $\beta\ge0$ (e.g. $H=-X_1-X_2$), so no entangled sequence exists and $\beta_{\mathrm{sep}}=+\infty$; the paper's witnesses (Theorem 35) are $3$-local, hence $k$-local for every $k\ge3$; also false at $k=2$ for the commuting converse: in a commuting $2$-local Pauli Hamiltonian two terms with different Paulis at a qubit $q$ must share their other qubit $a$, and then $\{q,a\}$ carries no other term, so $H$ is a direct sum of isolated pairs (dual degree $\le2$, $|c_a|\le1$, separable for $\beta$ below an absolute constant $c_0$) and a part with one Pauli axis per qubit (a locally rotated diagonal Hamiltonian, separable at every $\beta$); once $96\log2/(\mathfrak d+2)<c_0$ no such $H$ is entangled for all $\beta$ above it. The $\Theta$ clause is introduced by "Specifically" as (24) together with this converse, so it is stated on the same range
--   - reading: a sequence of commuting $k$-local Pauli Hamiltonians with dual degree $\mathfrak d$, entangled for all $\beta>96\log2/(\mathfrak d+2)$ → a sequence $H_j$ on `Fin (n j)` qubits, each $(\mathfrak d_j,3)$-low-intersection (so $|c_a|\le1$) and commuting, with $\mathfrak d_j$ its exact dual degree, $\mathfrak d_j\to\infty$, and one $H_j$ for every $\beta$ above its threshold; reason: $\Theta(1/\mathfrak d)$ is asymptotic in $\mathfrak d$ and the converse must lie in the family; the paper's sequence is $L\to\infty$ in Theorem 35
--   - reading: $\beta_{\mathrm{sep}}=\Theta(1/\mathfrak d)$ → $\exists C_1,C_2>0,\ \exists\mathfrak d_0,\ \forall\mathfrak d\ge\mathfrak d_0,\ \forall k\ge3:\ C_1/\mathfrak d\le\beta_{\mathrm{sep}}\le C_2/\mathfrak d$; reason: the standard meaning of $\Theta$ as $\mathfrak d\to\infty$, with constants uniform in $k$; for $\mathfrak d<1$ only Hamiltonians with pairwise disjoint terms qualify and $\beta_{\mathrm{sep}}=+\infty$
--   - encoding: Pauli Hamiltonian $H=\sum_{a\in A}c_aP_a$ on $n$ qubits with distinct non-identity strings → coefficient function $c$ on Pauli words of `Fin n` with $c(I)=0$, $A=\{P:c_P\neq0\}$; reason: distinctness is automatic and words with coefficient $0$ change neither $H$ nor any condition; no instance changes
--   - encoding: dual degree, $n\ge1$ in (9) → graph degree not counting the vertex itself; all $n\in\mathbb N$; reason: the paper's count $\mathfrak d=3L^D-2$ excludes the vertex; on $0$ qubits the Gibbs state is the $1\times1$ identity, a product state
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 1(b), eqs. (24)–(25), p.14; the converse family is Theorem 35, low-intersection bullet, p.84

import Mathlib
import Definitions.Def_QThermalClassical_ham
import Definitions.Def_QThermalClassical_gibbs
import Definitions.Def_QThermalClassical_IsSeparable
import Definitions.Def_QThermalClassical_IsCommutingPauli
import Definitions.Def_QThermalClassical_Supplement_IsLowIntersectionPauli
import Definitions.Def_QThermalClassical_Supplement_betaSepLI

set_option autoImplicit false

namespace QThermalClassical.Supplement

/-- **Theorem 1(b) (Death of entanglement, low-intersection Pauli Hamiltonians).**
1. For every `n`, all real `d, k > 0` and every `(d, k)`-low-intersection Pauli Hamiltonian
   `H` on `n` qubits, `ρ_β(H)` is separable whenever `0 ≤ β ≤ 1/(96d)` (24).
2. Conversely, there is a sequence of commuting `3`-local Pauli Hamiltonians `H_j`, each a
   `(d_j, 3)`-low-intersection Hamiltonian with `d_j` its dual degree, `d_j → ∞`, such that
   `ρ_β(H_j)` is entangled for all `β > 96 log 2/(d_j + 2)` (25).
3. `β_sep = Θ(1/d)`: there are `C₁, C₂ > 0` and `d₀` with `C₁/d ≤ β_sep ≤ C₂/d` for every real
   `d ≥ d₀` and every integer `k ≥ 3`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 1(b), eqs. (24)–(25), p.14; the converse family is Theorem 35's
low-intersection bullet, p.84.

**Formalization Note.** "`k`-local with dual degree `d`" in the converse is stated for
`k = 3` (the paper's witnesses are 3-local, hence `k`-local for every `k ≥ 3`), with `d` the
exact maximum degree of the dual interaction graph; the converse cannot hold for `k = 1` (a
1-local Hamiltonian has a product Gibbs state at every `β`). The `Θ` clause is asymptotic in
`d` and stated for integers `k ≥ 3`, the range of the converse; `log` is the natural log. -/
theorem theorem_1_b :
    (∀ (n : ℕ) (d k : ℝ), 0 < d → 0 < k → ∀ c : PauliWord (Fin n) → ℝ,
      IsLowIntersectionPauli d k c → ∀ β : ℝ, 0 ≤ β → β ≤ 1 / (96 * d) →
        IsSeparable (gibbs (ham c) β)) ∧
    (∃ (n : ℕ → ℕ) (c : ∀ j : ℕ, PauliWord (Fin (n j)) → ℝ),
      Filter.Tendsto (fun j => dualDegree (c j)) Filter.atTop Filter.atTop ∧
      ∀ j : ℕ, IsLowIntersectionPauli (dualDegree (c j) : ℝ) 3 (c j) ∧ IsCommutingPauli (c j) ∧
        ∀ β : ℝ, 96 * Real.log 2 / ((dualDegree (c j) : ℝ) + 2) < β →
          ¬ IsSeparable (gibbs (ham (c j)) β)) ∧
    (∃ C₁ C₂ d₀ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ d : ℝ, d₀ ≤ d → ∀ k : ℕ, 3 ≤ k →
      C₁ / d ≤ betaSepLI d (k : ℝ) ∧ betaSepLI d (k : ℝ) ≤ C₂ / d) := by sorry

end QThermalClassical.Supplement
