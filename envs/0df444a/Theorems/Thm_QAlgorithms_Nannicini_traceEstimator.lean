-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_traceEstimator
-- name    : QAlgorithms.Nannicini.traceEstimator
-- status  : Disproved
-- author  : @Goku
-- created : 2026-10-13T17:54:06.638703+00:00
-- url     : https://prove2.me/theorems/8bb74e38-1021-45c4-8c7b-e945224e11df
-- title:
--   One-copy trace estimator: a random variable with bias ≤ θ/4 for Tr(Aρ) and constant variance
-- statement:
--   There are absolute constants $C > 0$ and $c \in \mathbb{N}$ such that the following holds. Let $q, a \in \mathbb{N}$, $\alpha > 0$ and $\theta > 0$, and write
--
--   $$
--   L = \log(2 + \alpha) + \log(2 + 1/\theta) + \log(2 + q) + \log(2 + a).
--   $$
--
--   There exist a number $w$ of ancilla qubits, a quantum circuit $\mathcal{V}$ on $q + w$ qubits with oracle calls to an $(a+q)$-qubit unitary $U$ (and $U^\dagger$), and a function $Y : \{0,1\}^{q+w} \to \mathbb{R}$, all depending only on $q, a, \alpha, \theta$, such that $\mathcal{V}$ makes at most $C(\alpha+1)L^c$ calls to $U$ or $U^\dagger$ and uses at most $C(\alpha+1)(a+1)L^c$ two-qubit gates, and such that for every Hermitian real matrix $A \in \mathbb{R}^{2^q \times 2^q}$ with $\|A\| \le 1$, every $(\alpha, a, \theta/2)$-block-encoding $U$ of $A$, and every $q$-qubit density matrix $\rho$ the following holds. Let
--
--   $$
--   \sigma = \mathcal{V}(U)\,\bigl(\rho \otimes |0\rangle\langle 0|_w\bigr)\,\mathcal{V}(U)^\dagger,
--   $$
--
--   measure all qubits of $\sigma$ in the computational basis, obtaining $z$ with probability $\langle z|\sigma|z\rangle$, and output $Y(z)$. Then
--
--   $$
--   \bigl|\mathbb{E}[Y] - \operatorname{Tr}(A\rho)\bigr| \le \frac{\theta}{4}, \qquad \operatorname{Var}[Y] \le C .
--   $$
--
--   Repeating this one-copy estimator and averaging gives estimates of $\operatorname{Tr}(A\rho)$, the basic primitive of quantum SDP solvers.
--
--   **Formalization Note** $\widetilde{O}(\alpha)$ is unfolded as $C(\alpha+1)L^c$ with constants quantified before all parameters; the polylogarithmic factor $L$ involves $\theta$, $q$ and $a$ as well, since the source's Def. 1.11 lets the $\widetilde{O}$ polylog depend on other instance parameters; $\alpha + 1$ because $\alpha$ may be below $1$. The standard deviation $\sigma = O(1)$ is stated as a variance bound by the same absolute constant. The block-encoding has its auxiliary register first. The gate bound carries a factor $a+1$ that the source's $\widetilde{O}(\alpha)$ omits: the construction reflects about $|0\rangle_a$ once per use of $U$, as in the cited result's $O(a\alpha\log(1/\theta))$; the discrepancy is recorded in the docstring and in HARD.md. Calls to $U$ may be controlled.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 173, Proposition 7.41. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_QAlgorithms_Nannicini_Ch07b_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini



/-- Nannicini p.173, Proposition 7.41 (Cor. 6.4.5 in [Gilyén, 2019]). Let `ρ` be a `q`-qubit
density matrix and `U` an `(α, a, θ/2)`-block-encoding of a Hermitian matrix
`A ∈ ℝ^{2^q × 2^q}` with `‖A‖ ≤ 1`. A quantum circuit (fixed before `A`, `U`, `ρ`) acting on one
copy of `ρ` and `w` ancillas in `|0⟩`, followed by a measurement of all qubits and a classical
map `Y` of the outcome (Rem. 7.42), outputs a sample of a random variable `Y` with
`|E[Y] − Tr(Aρ)| ≤ θ/4` and `Var[Y] ≤ C` (`σ = O(1)`). It uses `Õ(α)` applications of `U`
and `U†` and `Õ(α)` two-qubit gates, with
`Õ(α) = C(α + 1)(log(2 + α) + log(2 + 1/θ) + log(2 + q) + log(2 + a))^c` (Def. 1.11, p.11: the
polylog factor may also depend on the other instance parameters `θ`, `q`, `a`).

Discrepancy with the page (trap 30): the gate count carries a factor `a + 1` (the number of
auxiliary qubits of `U`). Every block-encoding manipulation of the proof (amplification,
polynomial transformations) reflects about `|0⟩_a` once per use of `U`, which costs `Θ(a)`
two-qubit gates; the source's own Prop. 7.38 counts `Õ(√n β a)` gates, and the cited result
counts `O(a α log(1/θ))`. A bound `Õ(α)` polylogarithmic in `a` is not what the construction
gives. -/
theorem traceEstimator :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ (q a : ℕ) (α θ : ℝ), 0 < α → 0 < θ →
      ∃ (w : ℕ) (V : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => a + q) (q + w))
        (Y : Qubits (q + w) → ℝ),
        (V.queryCount 0 : ℝ) ≤ C * (α + 1) * (Real.log (2 + α) + Real.log (2 + 1 / θ) +
          Real.log (2 + (q : ℝ)) + Real.log (2 + (a : ℝ))) ^ c ∧
        (V.gateCount : ℝ) ≤
          C * (α + 1) * ((a : ℝ) + 1) * (Real.log (2 + α) + Real.log (2 + 1 / θ) +
            Real.log (2 + (q : ℝ)) + Real.log (2 + (a : ℝ))) ^ c ∧
        ∀ (A : Matrix (Qubits q) (Qubits q) ℂ) (U : Matrix (Qubits (a + q)) (Qubits (a + q)) ℂ)
          (ρ : Matrix (Qubits q) (Qubits q) ℂ),
          A.IsHermitian → (∀ i j, (A i j).im = 0) → specNorm A ≤ 1 →
          IsBlockEncoding (0 : Qubits a)
            (U.submatrix (qubitsAppendEquiv a q).symm (qubitsAppendEquiv a q).symm) α (θ / 2) A →
          IsDensityMatrix ρ →
          |densityMean ((V.unitary fun _ => U) * withZeroAncillas ρ w *
              star (V.unitary fun _ => U)) Y - (A * ρ).trace.re| ≤ θ / 4 ∧
          densityVariance ((V.unitary fun _ => U) * withZeroAncillas ρ w *
              star (V.unitary fun _ => U)) Y ≤ C := by
  sorry










end QAlgorithms.Nannicini
