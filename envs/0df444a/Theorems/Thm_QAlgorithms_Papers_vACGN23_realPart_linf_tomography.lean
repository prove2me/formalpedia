-- Prove2me | Theorems.Thm_QAlgorithms_Papers_vACGN23_realPart_linf_tomography
-- name    : QAlgorithms.Papers.vACGN23.realPart_linf_tomography
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T18:49:05.305309+00:00
-- url     : https://prove2.me/theorems/0dc76851-13d1-4973-aa73-2795db5e5252
-- title:
--   Pure-state tomography of Re(α) in ℓ∞-norm with a state-preparation unitary
-- statement:
--   This is the $\ell_\infty$ pure-state tomography result of van Apeldoorn, Cornelissen, Gilyén and Nannicini (arXiv:2207.08800, Proposition 22), cited in Nannicini's lecture notes as Theorem 5.17.
--
--   Let $d\ge 1$ and $n=\lceil\log_2 d\rceil$. Let $|\psi\rangle=\sum_{j=0}^{d-1}\alpha_j|j\rangle$ be a pure state, so $\alpha\in\mathbb C^d$ and $\|\alpha\|_2=1$. It is stored on $n$ qubits, with basis states $|j\rangle$ for $j\ge d$ having amplitude $0$. Let $U$ be an $n$-qubit unitary with $U|0\rangle=|\psi\rangle$. The algorithm can apply $U$ and $U^\dagger$, possibly controlled, but sees $U$ only through these applications. The gate set has all single-qubit gates, CNOT, and the indexed-SWAP gate
--
--   $$\text{indexed-SWAP}\,|i\rangle|j\rangle|x_1\rangle\cdots|x_D\rangle=|i\rangle|j\rangle\,\mathrm{SWAP}_{i,j}(|x_1\rangle\cdots|x_D\rangle).$$
--
--   There are absolute constants $C>0$ and $c\in\mathbb N$ such that the following holds for every $d\ge1$, $\varepsilon>0$ and $\delta\in(0,1)$. Write $L=\log(2+d)+\log(2+1/\varepsilon)+\log(2+1/\delta)$.
--
--   1. There is a quantum algorithm, fixed before $U$, with the following resources:
--      - at most $C\,\frac{\sqrt d}{\varepsilon}\log(2+d/\delta)$ applications of $U$ and $U^\dagger$;
--      - at most $C\,\frac{\sqrt d}{\varepsilon}\log(2+d/\delta)\log(2+d/\varepsilon)$ indexed-SWAP gates, each acting on a memory of $d$ qubits;
--      - at most $C\,(d+\sqrt d/\varepsilon)L^c$ additional gates (single-qubit gates and CNOTs).
--
--      For every such $\psi$ and $U$, with probability at least $1-\delta$ it outputs $\tilde\alpha\in\mathbb R^d$ with
--   $$\|\mathrm{Re}(\alpha)-\tilde\alpha\|_\infty\le\varepsilon.$$
--   2. If $\varepsilon\ge1/\sqrt d$, there is such an algorithm with at most $C\,L^c/\varepsilon^2$ applications of $U$ and $U^\dagger$ and at most $C\,L^c/\varepsilon^4$ gates in total, with the same guarantee.
--
--   The result reaches the optimal $\sqrt d/\varepsilon$ dependence for $\ell_\infty$-estimation of the amplitudes. Combined with the paper's $\ell_\infty$-to-$\ell_q$ conversion, it yields the $\ell_q$ tomography bounds (Theorem 23 of the paper; Corollary 5.18 in Nannicini).
--
--   **Formalization Note** Both clauses use the coherent-circuit model: one oracle circuit over the paper's gate set, started in $|0\rangle$ and measured once, with classical post-processing (medians, rescaling) in a read-out function. The paper allows adaptive classical control. The adaptive algorithm of clause 2 is simulated by deferred measurement, and the paper's convention of counting classical computation up to polylog factors absorbs the cost. The logarithms $\log(d/\delta)$ and $\log(d/\varepsilon)$ are written $\log(2+\cdot)$ so the bounds do not vanish in the degenerate corner $d=1$, $\delta\to1$. The $\tilde O$ factors are $L^c$. On index values $\ge D$, which the paper leaves unspecified, the indexed-SWAP gate acts as the identity.
-- source:
--   Quantum tomography using state-preparation unitaries (van Apeldoorn, Cornelissen, Gilyén, Nannicini), arXiv:2207.08800v1, Proposition 22, PDF p. 22. https://arxiv.org/abs/2207.08800v1 . PDF SHA-256: 1a52a38605ad589f5bf85cf50986e861e6b8be7322a51244b75fa5ad50e9aac9.

import Definitions.Def_QAlgorithms_Defs_CircuitResources
set_option autoImplicit false

namespace QAlgorithms.Papers.vACGN23

/-- 2207.08800 p.22–23, Proposition 22 (cited by Nannicini as Theorem 5.17). "Let
`|ψ⟩ = Σ_{j∈[d]} α_j |j⟩` be a quantum state, and `U|0⟩ = |ψ⟩`. There is a quantum algorithm that,
with probability at least `1 − δ`, outputs `α̃ ∈ ℝ^d` such that `‖ℜ(α) − α̃‖_∞ ≤ ε`, using
`O((√d/ε) log(d/δ))` applications of `U` and `U†`, `O((√d/ε) log(d/δ) log(d/ε))` indexed-SWAP gates
acting on `d` bits, and `Õ(d + √d/ε)` additional gates. If `ε ≥ 1/√d`, the number of applications
of `U` can be reduced to `Õ(1/ε²)` (while potentially increasing the gate complexity to
`Õ(1/ε⁴)`)."

Formal reading. There are constants `C > 0` and `c` (fixed before `d, ε, δ`) such that for every
`d ≥ 1`, `ε > 0` and `δ ∈ (0, 1)`:

1. there is an oracle circuit over `vacgnGateSet` on `w` qubits started in `|0⟩`, with oracle
   calls to an `n`-qubit unitary, and a classical read-out `out` of the final measurement, such
   that the number of oracle calls (applications of `U` or `U†`, controlled or not) is at most
   `C (√d/ε) log(2 + d/δ)`, every gate is a single-qubit gate, a CNOT or an indexed-SWAP gate on
   a memory of exactly `d` qubits, the number of the latter is at most
   `C (√d/ε) log(2 + d/δ) log(2 + d/ε)` and the number of the former ("additional gates") is at
   most `C (d + √d/ε) L^c`, `L = log(2 + d) + log(2 + 1/ε) + log(2 + 1/δ)`; and for **every** unit
   vector `α ∈ ℂ^d` and every unitary `U` with `U|0⟩ = |ψ⟩`, the measured outcome `z` satisfies
   `|ℜ(α_j) − out(z)_j| ≤ ε` for all `j` with probability at least `1 − δ`;
2. if `ε ≥ 1/√d`, there is such a circuit (with indexed-SWAP gates of any memory size) with at
   most `C (1/ε²) L^c` oracle calls and at most `C (1/ε⁴) L^c` gates in total, with the same
   success guarantee.

The paper's computer may adapt its gates to intermediate measurements (p.6). The algorithm of
clause 1 is non-adaptive; that of clause 2 measures first and then runs clause 1 on the observed
indices. Both are stated in the coherent-circuit model (one circuit, one final measurement,
classical post-processing such as medians and rescaling in `out`); by deferred measurement this
costs only the reversible simulation of the classical control, which the paper's convention
(classical computation counted up to polylog factors) absorbs into the `Õ`. The logarithms
`log(d/δ)`, `log(d/ε)` are taken as `log(2 + ·)` so that the `O`-bounds do not vanish at the
degenerate corner `d = 1`, `δ → 1` (the base of the logarithm is absorbed in `C`). -/
theorem realPart_linf_tomography :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (ε δ : ℝ), 0 < ε → 0 < δ → δ < 1 →
      (∃ (w : ℕ) (circ : OracleCircuit vacgnGateSet (fun _ : Fin 1 => Nat.clog 2 d) w)
          (out : Qubits w → Fin d → ℝ),
        (circ.queryCount 0 : ℝ) ≤ C * (Real.sqrt d / ε) * Real.log (2 + d / δ) ∧
          circ.gateCount ≤
            circ.gateCountWhere (fun g => (∃ M : Matrix Bool Bool ℂ,
                M ∈ Matrix.unitaryGroup Bool ℂ ∧ g = Gate.ofMatrix1 M) ∨ g = Gate.ofMatrix2 cnot) +
              circ.gateCountWhere (fun g => g = indexedSwapGate d) ∧
          (circ.gateCountWhere (fun g => g = indexedSwapGate d) : ℝ) ≤
            C * (Real.sqrt d / ε) * Real.log (2 + d / δ) * Real.log (2 + d / ε) ∧
          (circ.gateCountWhere (fun g => (∃ M : Matrix Bool Bool ℂ,
                M ∈ Matrix.unitaryGroup Bool ℂ ∧ g = Gate.ofMatrix1 M) ∨
              g = Gate.ofMatrix2 cnot) : ℝ) ≤
            C * (d + Real.sqrt d / ε) *
              (Real.log (2 + d) + Real.log (2 + 1 / ε) + Real.log (2 + 1 / δ)) ^ c ∧
          ∀ α : EuclideanSpace ℂ (Fin d), ‖α‖ = 1 →
            ∀ U ∈ Matrix.unitaryGroup (Qubits (Nat.clog 2 d)) ℂ,
              act U (zeroKet (Nat.clog 2 d)) = padState (Nat.clog 2 d) α →
              1 - δ ≤ probEvent (act (circ.unitary fun _ => U) (zeroKet w))
                fun z => ∀ j : Fin d, |(α j).re - out z j| ≤ ε) ∧
      (1 / Real.sqrt d ≤ ε →
        ∃ (w : ℕ) (circ : OracleCircuit vacgnGateSet (fun _ : Fin 1 => Nat.clog 2 d) w)
          (out : Qubits w → Fin d → ℝ),
          (circ.queryCount 0 : ℝ) ≤ C * (1 / ε ^ 2) *
              (Real.log (2 + d) + Real.log (2 + 1 / ε) + Real.log (2 + 1 / δ)) ^ c ∧
            (circ.gateCount : ℝ) ≤ C * (1 / ε ^ 4) *
              (Real.log (2 + d) + Real.log (2 + 1 / ε) + Real.log (2 + 1 / δ)) ^ c ∧
            ∀ α : EuclideanSpace ℂ (Fin d), ‖α‖ = 1 →
              ∀ U ∈ Matrix.unitaryGroup (Qubits (Nat.clog 2 d)) ℂ,
                act U (zeroKet (Nat.clog 2 d)) = padState (Nat.clog 2 d) α →
                1 - δ ≤ probEvent (act (circ.unitary fun _ => U) (zeroKet w))
                  fun z => ∀ j : Fin d, |(α j).re - out z j| ≤ ε) := by
  sorry

end QAlgorithms.Papers.vACGN23
