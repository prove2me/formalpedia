-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_stateTomography_euclidean
-- name    : QAlgorithms.Nannicini.stateTomography_euclidean
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:46:46.690829+00:00
-- url     : https://prove2.me/theorems/b8cae3c0-52d9-41f6-91de-3910c1fcc812
-- title:
--   Pure-state tomography with Euclidean error using Õ(d/ϵ) uses of U
-- statement:
--   This corollary is pure-state tomography with Euclidean error.
--
--   Let $U$ be a unitary on $n$ qubits with $U|0\rangle = |\psi\rangle = \sum_{j\in\{0,1\}^n}\alpha_j|j\rangle$, and let $d = 2^n$. For accuracy $\epsilon > 0$ and failure probability $\delta \in (0,1)$, there is a quantum algorithm that outputs $\tilde\alpha \in \mathbb R^d$ with
--
--   $$
--   \Pr\big[\|\operatorname{Re}(\alpha) - \tilde\alpha\|_2 \le \epsilon\big] \ge 1 - \delta,
--   $$
--
--   using $\tilde O(d/\epsilon)$ applications of $U$ and $U^\dagger$ and $\tilde O(d^2/\epsilon)$ additional gates. A second algorithm with the same resources outputs $\tilde\alpha$ with $\|\operatorname{Im}(\alpha) - \tilde\alpha\|_2 \le \epsilon$ with the same probability.
--
--   Precisely, there are constants $C > 0$ and $c \in \mathbb N$ such that the following holds. For all $n$, $\epsilon > 0$ and $\delta \in (0,1)$, there are a quantum circuit over the gate set $\{H, T, \mathrm{CX}\}$ (Theorem 1.43) and a classical read-out of its measured workspace, both independent of $U$. The circuit accesses $U$ only through calls to $U$ or $U^\dagger$, possibly controlled. It makes at most $C\,(d/\epsilon)\,L$ such calls and uses at most $C\,(d^2/\epsilon)\,L$ gates, where
--
--   $$
--   L = \big(\log(2 + d/\epsilon) + \log(2 + 1/\delta)\big)^c.
--   $$
--
--   The error guarantee above holds for every unitary $U$.
--
--   The result turns any algorithm that prepares its answer as a quantum state into one with a classical output vector, at a cost linear in the dimension.
--
--   **Formalization Note** The polylogarithmic factor of $\tilde O$ (Definition 1.11) is written as a power of $\log(2+d/\epsilon)+\log(2+1/\delta)$. The circuit is an `OracleCircuit` with a single oracle, and `queryCount` counts every call to $U$, adjoint or controlled. The circuit is quantified before $U$. Classical post-processing of the measurement outcome is not counted.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 117, Corollary 5.18. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Nannicini_Ch05a_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini




/-- Nannicini p.117, Corollary 5.18 (pure-state tomography with Euclidean error). Let
`U|0⟩ = |ψ⟩ = ∑_{j ∈ {0,1}^n} α_j |j⟩` and `d = 2^n`. With probability at least `1 − δ` one
outputs `α̃ ∈ ℝ^d` with `‖Re(α) − α̃‖ ≤ ϵ` using `Õ(d/ϵ)` applications of `U` and `U†` and
`Õ(d²/ϵ)` additional gates; a small modification outputs `α̃` with `‖Im(α) − α̃‖ ≤ ϵ` with the
same running time. Formally: there are constants `C > 0` and `c` such that for every `n`, every
`ϵ > 0` and every `δ ∈ (0, 1)` there is an oracle circuit over the gate set `{H, T, CX}` of
Thm. 1.43, on a workspace of `w` qubits started in `|0⟩`, with oracle calls to `U` (possibly
controlled, possibly adjoint), together with a classical read-out `out` of the measured
workspace, using at most `C (d/ϵ) L` oracle calls and `C (d²/ϵ) L` gates, where
`L = (log(2 + d/ϵ) + log(2 + 1/δ))^c` is the polylogarithmic factor of `Õ` (Def. 1.11), such that
for **every** unitary `U` on `n` qubits the Euclidean error `‖Re(α) − out(z)‖ ≤ ϵ` holds with
probability at least `1 − δ`; and a second such circuit for `Im(α)`. The circuit is chosen before
`U` and sees `U` only through its oracle calls (trap Q2). -/
theorem stateTomography_euclidean :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ ∀ (n : ℕ) (ε δ : ℝ), 0 < ε → 0 < δ → δ < 1 →
      (∃ (w : ℕ) (circ : OracleCircuit htcxGateSet (fun _ : Fin 1 => n) w)
          (out : Qubits w → Qubits n → ℝ),
        (circ.queryCount 0 : ℝ) ≤
            C * ((2 : ℝ) ^ n / ε) * (Real.log (2 + (2 : ℝ) ^ n / ε) + Real.log (2 + 1 / δ)) ^ c ∧
          (circ.gateCount : ℝ) ≤
            C * (((2 : ℝ) ^ n) ^ 2 / ε) *
              (Real.log (2 + (2 : ℝ) ^ n / ε) + Real.log (2 + 1 / δ)) ^ c ∧
          ∀ U ∈ Matrix.unitaryGroup (Qubits n) ℂ,
            1 - δ ≤ probEvent (act (circ.unitary fun _ => U) (zeroKet w))
              fun z => Real.sqrt (∑ j, ((act U (zeroKet n) j).re - out z j) ^ 2) ≤ ε) ∧
      (∃ (w : ℕ) (circ : OracleCircuit htcxGateSet (fun _ : Fin 1 => n) w)
          (out : Qubits w → Qubits n → ℝ),
        (circ.queryCount 0 : ℝ) ≤
            C * ((2 : ℝ) ^ n / ε) * (Real.log (2 + (2 : ℝ) ^ n / ε) + Real.log (2 + 1 / δ)) ^ c ∧
          (circ.gateCount : ℝ) ≤
            C * (((2 : ℝ) ^ n) ^ 2 / ε) *
              (Real.log (2 + (2 : ℝ) ^ n / ε) + Real.log (2 + 1 / δ)) ^ c ∧
          ∀ U ∈ Matrix.unitaryGroup (Qubits n) ℂ,
            1 - δ ≤ probEvent (act (circ.unitary fun _ => U) (zeroKet w))
              fun z => Real.sqrt (∑ j, ((act U (zeroKet n) j).im - out z j) ^ 2) ≤ ε) := by
  sorry




end QAlgorithms.Nannicini
