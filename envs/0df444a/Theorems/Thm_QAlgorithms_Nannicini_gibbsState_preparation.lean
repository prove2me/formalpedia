-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_gibbsState_preparation
-- name    : QAlgorithms.Nannicini.gibbsState_preparation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:52:50.964644+00:00
-- url     : https://prove2.me/theorems/c2ad1a30-43b3-4df2-99e4-246dfb50a6cb
-- title:
--   Gibbs-state preparation from a block-encoding of H, for the polynomial of Lemma 7.37 made explicit
-- statement:
--   Fix constants $C_0 \in \mathbb{R}$ and $c_0 \in \mathbb{N}$ (the constants of the $\widetilde{O}(\beta)$ degree bound of Lemma 7.37). There are constants $C > 0$ and $c \in \mathbb{N}$ such that the following holds. Let $q, a \in \mathbb{N}$, $n = 2^q$, $\theta \in (0, 1/3]$ and $\beta > 1$, and put $\xi = \theta/(128 n)$. Let $P$ be any real polynomial with the properties of Lemma 7.37 at this $\xi$:
--
--   1. $|P(x) - e^{2\beta x}/4| \le \xi$ for all $x \in [-1, 0]$;
--   2. $|P(x)| \le 1/2$ for all $x \in [-1, 1]$;
--   3. $\deg P \le C_0\,\beta\,(\log(2+\beta) + \log(2 + 1/\xi))^{c_0}$,
--
--   and let $d = \deg P$. Write $L = \log(2+n) + \log(2+\beta) + \log(2+1/\theta) + \log(2+a)$. Then there is a quantum circuit $\mathcal{V}$ on $q + m$ qubits (for some $m$), depending only on $q, a, \theta, \beta, P$, that makes at most $C\sqrt{n}\,\beta\,L^c$ calls to an $(a+q)$-qubit unitary $U$ or its inverse and uses at most $C\sqrt{n}\,\beta\,(a+1)\,L^c$ two-qubit gates, such that for every real Hermitian matrix $H \in \mathbb{R}^{n\times n}$ and every $(\beta, a, \theta^2\beta/(1024^2 d^2 n^2))$-block-encoding $U$ of $H$, the pure state $\mathcal{V}(U)|0\rangle$ is a purification of a state $\tilde\rho$ (its partial trace over the last $m$ qubits) with
--
--   $$
--   \Bigl\| \tilde\rho - \frac{e^{H}}{\operatorname{Tr} e^{H}} \Bigr\|_{\mathrm{Tr}} \le \theta .
--   $$
--
--   Gibbs states are the iterates of matrix multiplicative weights; this result turns a block-encoding of the Hamiltonian into a preparation of the corresponding Gibbs state, the core subroutine of quantum SDP solvers.
--
--   **Formalization Note** Corrected statement. The source's $d$ is "the degree of the polynomial from Lemma 7.37", which only asserts that some polynomial of degree $\widetilde{O}(\beta)$ exists; here the polynomial is an explicit parameter, universally quantified, with its degree constants quantified before the theorem's. The source's proof sketch assumes $n = 2^q$, as does the statement. The gate bound has $a+1$ in place of $a$, so it is not $0$ at $a = 0$. The trace norm is the sum of singular values (Def. 7.31); the block-encoding has its auxiliary register first (Def. 7.11).
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 171, Proposition 7.38. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_QAlgorithms_Nannicini_Ch07b_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini





/-- Corrected statement. Nannicini p.171, Proposition 7.38 (Lem. 4.15 in [van Apeldoorn, 2020]),
as printed: "Let `H ∈ ℝ^{n×n}` be a Hermitian matrix. Let `θ ∈ (0, 1/3]`, `β > 1`, and let `d`
be the degree of the polynomial from Lemma 7.37 when we let `ξ = θ/(128n)`. Let `U` be a
`(β, a, θ²β/(1024² d² n²))`-block-encoding of `H`. Then we can create a purification of a state
`ρ̃` such that `‖ρ̃ − exp(H)/Tr(exp(H))‖_Tr ≤ θ` using `Õ(√n β)` applications of `U` and
`Õ(√n β a)` elementary gates."

What was changed. (1) "The polynomial from Lemma 7.37" is a named parameter `P`: the statement
holds for every real polynomial with the three properties of Lemma 7.37 at `ξ = θ/(128n)`,
the degree bound `deg P ≤ C₀ β (log(2+β) + log(2+1/ξ))^{c₀}` (Lemma 7.37's `Õ(β)`) being stated
with constants `C₀, c₀` quantified universally before the theorem's own constants; `d` is
`deg P`, and the circuit may depend on `P` (it implements `P` by singular value transformation,
p.171–172). (2) `n = 2^q`, the case the source's own construction treats ("assume `n = 2^q` for
simplicity", p.171–172); a matrix of non-power-of-two size has no qubit block-encoding without a
padding convention the source does not give. (3) The gate bound carries `(a + 1)` instead of `a`,
so that it is not `0` at `a = 0`. (4) `Õ(·)` is `C · (·) · L^c` with
`L = log(2+n) + log(2+β) + log(2+1/θ) + log(2+a)` (Def. 1.11).

Why. Lemma 7.37 asserts only that some polynomial of degree `Õ(β)` exists, so "its degree `d`"
is not determined. The construction uses one such polynomial and needs the block-encoding
precision for the degree of the polynomial it uses; the universally quantified `P` is that
reading, made explicit.

Precision formulas checked against the rendered PDF page p.171 (2026-10-09): `ξ = θ/(128n)`,
block-encoding error `θ²β/(1024² d² n²)`, `θ ∈ (0, 1/3]` (closed at `1/3`, as in the rendered
page and the text layer). The first statement of this item had `θ²/(128n)` and
`θ²/(1024 d β² n²)`, read from a garbled text extraction.

Model. "Elementary gates" are two-qubit gates (`twoQubitGateSet`, as for Prop. 7.41). The circuit
acts on the `q` system qubits and `m` further qubits, all starting in `|0⟩`, and calls `U`
(acting on `a + q` qubits, auxiliary register first as in Def. 7.11) and `U†`. The created pure
state `V(U)|0⟩` is a purification (Def. 1.69) of `ρ̃`: `ρ̃` is its partial trace over the last
`m` qubits. `H` is real (`H ∈ ℝ^{n×n}`) and Hermitian. The Gibbs state is the frozen
`gibbsState` (Def. 7.34), the trace norm is `traceNorm` (Def. 7.31). -/
theorem gibbsState_preparation :
    ∀ (C₀ : ℝ) (c₀ : ℕ), ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ (q a : ℕ) (θ β : ℝ), 0 < θ → θ ≤ 1 / 3 →
      1 < β → ∀ P : Polynomial ℝ,
      (∀ x ∈ Set.Icc (-1 : ℝ) 0,
        |P.eval x - Real.exp (2 * β * x) / 4| ≤ θ / (128 * (2 : ℝ) ^ q)) →
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1 / 2) →
      (P.natDegree : ℝ) ≤
        C₀ * β * (Real.log (2 + β) + Real.log (2 + 1 / (θ / (128 * (2 : ℝ) ^ q)))) ^ c₀ →
      ∃ (m : ℕ) (V : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => a + q) (q + m)),
        (V.queryCount 0 : ℝ) ≤ C * Real.sqrt ((2 : ℝ) ^ q) * β *
          (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + β) + Real.log (2 + 1 / θ) +
            Real.log (2 + (a : ℝ))) ^ c ∧
        (V.gateCount : ℝ) ≤ C * Real.sqrt ((2 : ℝ) ^ q) * β * ((a : ℝ) + 1) *
          (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + β) + Real.log (2 + 1 / θ) +
            Real.log (2 + (a : ℝ))) ^ c ∧
        ∀ (H : Matrix (Qubits q) (Qubits q) ℂ) (U : Matrix (Qubits (a + q)) (Qubits (a + q)) ℂ),
          H.IsHermitian → (∀ i j, (H i j).im = 0) →
          IsBlockEncoding (0 : Qubits a)
            (U.submatrix (qubitsAppendEquiv a q).symm (qubitsAppendEquiv a q).symm) β
            (θ ^ 2 * β / (1024 ^ 2 * (P.natDegree : ℝ) ^ 2 * ((2 : ℝ) ^ q) ^ 2)) H →
          traceNorm (traceRight (pureDensity (WithLp.toLp 2 fun z : Qubits q × Qubits m =>
              act (V.unitary fun _ => U) (zeroKet (q + m)) ((qubitsAppendEquiv q m).symm z))) -
            gibbsState H) ≤ θ := by
  sorry








end QAlgorithms.Nannicini
