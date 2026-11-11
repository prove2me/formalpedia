-- Prove2me | Theorems.Thm_QuadSDE_theorem_2
-- name    : QuadSDE.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:31.215291+00:00
-- url     : https://prove2.me/theorems/c803c7a1-4115-4d2b-a678-7ea43468b522
-- title:
--   Theorem 2 — quantum algorithm for APX-SDE: $|\hat v-\mathbb E\,u_0(X(T))|\le\epsilon$ w.p. $\ge2/3$ with $\mathrm{poly}(T,\log N,J,r,\epsilon^{-1},p^{-1},q^{-1})\,e^{2\|Y\|^2/p}$ gates and queries
-- statement:
--   Consider APX-SDE in the oracle-based input model. An instance consists of the classical data $N$, $r\ge1$, $J>0$, $0<p,q\le1$, $T\ge0$, $\epsilon>0$, $\|Y\|^2>0$, an observable $u_0\in\mathcal O$ and the ancilla sizes $a_V,a_P$ of the oracles, together with hidden data: an admissible quadratic drift $c$ (symmetric, norm and volume preserving) with strength at most $J$ and at most $r$ channels, and $Y\in\mathbb R^N$ with the given norm. The hidden data are accessible only through unitary oracles $\mathsf{Val}_c$, $\mathsf{Pos}_c$, $\mathsf{Val}_Y$ satisfying Eqs. (18)–(20), with arbitrary junk, and their inverses and controlled versions.
--
--   There is one uniform quantum algorithm $A$ (a classical constructor writing, from the classical data, a program of gates from $\{H,T,\mathrm{CNOT}\}$, oracle calls, measurements and classical steps) and there are constants $C,K$ such that for every instance, every valid oracle triple, every probability space carrying the noise $(W,Z)$ of Eq. (2), and every solution $X$ of
--   $$dX(t)=f(X(t))\,dt+\sqrt q\,dW(t),\qquad X(0)=Y+\sqrt p\,Z$$
--   on $[0,T]$:
--   1. $u_0(X(T))$ is integrable;
--   2. the program outputs a real number $\hat v$ with
--   $$\Pr\big[|\hat v-\mathbb E_{\mathrm{noise}}u_0(X(T))|\le\epsilon\big]\ge\frac23;$$
--   3. it uses at most
--   $$C\big(1+T+\log_2(N+1)+J+r+\epsilon^{-1}+p^{-1}+q^{-1}+a_V+a_P\big)^K\exp\Big(\frac{2\|Y\|^2}p\Big)\qquad(24)$$
--   elementary gates, oracle queries and other charged operations;
--   4. it uses at most
--   $$C\big(1+T+\log_2(N+1)+J+r+\log_2(1+\epsilon^{-1})+p^{-1}+q^{-1}+\|Y\|+a_V+a_P\big)^K\qquad(25)$$
--   qubits, including ancillas.
--
--   This is the formal version of Theorem 1(i): for $\|Y\|=O(1)$, $p,q\ge\Omega(1/\log\log N)$, $T\le\mathrm{poly}(\log N)$ and $\epsilon\ge1/\mathrm{poly}(\log N)$ the algorithm runs in time $\mathrm{poly}(\log N)$, while the noise-free problem is PP-hard.
--
--   Differences from the source:
--   - reading: a quantum algorithm that takes as input an instance … in the oracle-based input model … using … elementary quantum gates and oracle queries → a QAlgorithms.OPI.UniformResourceFamily: one public classical constructor that writes, from the classical data only, an adaptive program over {H, T, CNOT} calling Val_c, Pos_c, Val_Y (inverse and controlled calls allowed); its cost is membershipResources (qubits, classical bits, gates, queries, measurements, preparations, classical operations, worst case over branches); reason: p. 16 compiles rotation angles to finite precision, so a finite gate set; charging more operations than gates and queries is not weaker
--   - reading: poly(T, log N, J, r, ϵ⁻¹, p⁻¹, q⁻¹) exp(2‖Y‖²/p); poly(T, log N, J, r, log(ϵ⁻¹), p⁻¹, q⁻¹, ‖Y‖) → C (1 + T + log₂(N+1) + J + r + 1/ε + 1/p + 1/q + a_V + a_P)^K · exp(2‖Y‖²/p) and C (1 + T + log₂(N+1) + J + r + log₂(1 + 1/ε) + 1/p + 1/q + ‖Y‖ + a_V + a_P)^K, with C, K chosen after the algorithm and before every instance; reason: standard reading of poly(·); log₂(N+1) and log₂(1 + 1/ε) differ from log N and log(1/ϵ) only where these are ≤ 1, which the constant term absorbs; the exponential factor enters linearly
--   - reading: ancillary register A of poly(log N) qubits (p. 14) → its sizes a_V, a_P are part of the instance and enter both polynomials; reason: the program must hold the oracles' ancillas; with a_V, a_P ≤ poly(log N) this is the source's bound
--   - reading: the bound (24) on gates and oracle queries → the classical constructor runs within a polynomial budget in expansionScale, which includes the input length and ⌈exp(2‖Y‖²/p)⌉; the program's resources are bounded by (24) without them; reason: Eq. (24) counts the quantum algorithm's gates and queries, not the preprocessing that writes it out; the constructor must read its input and write a program of that size
--   - generalization: N, r, J, p, q, T, ϵ supplied explicitly in binary; ‖Y‖ supplied classically → J, p, q, T, ε arbitrary rationals; the norm supplied as the rational ‖Y‖²; reason: binary numbers are dyadic rationals; every rational ‖Y‖ has a rational square, and the succinct model itself supplies ‖Y‖² in binary (p. 16)
--   - generalization: oracle model of §3.2 with r ≤ poly(log N) (p. 14) and the drift parameters s, r, J supplied in binary (p. 13) → no bound on r is assumed and the sparsity s is not supplied (the input carries N, a_V, a_P, r, J, p, q, T, ε, ‖Y‖², u₀); reason: the bounds are stated in r itself, so instances with r ≤ poly(log N) are a special case, and an algorithm that is not told s also serves inputs that include it
--   - reading: outputs a real number v̂ → the output bits are read by decodeReal (sign bit, then 2L binary digits with L after the point); a failure leaf is never a success; reason: an output is a finite bit string; every dyadic rational is representable
--   - generalization: X(t) solves the SDE Eq. (2) ("a unique global strong solution", p. 17) → any process X on any probability space carrying (W, Z) that solves Eq. (2) pathwise (continuous paths, integral equation a.s.); reason: with additive noise and a locally Lipschitz drift every pathwise solution agrees a.s. with the strong solution, so the statement specializes to the source's
--   - encoding: E_noise u₀(X(T)) and Pr[…] → Bochner integral over the probability space with an explicit integrability conclusion; the probability is membershipOutputLaw of the success event; reason: Lean convention; the integrability clause rules out the junk value 0 of a non-integrable integral
--   - encoding: Val_c, Pos_c, Val_Y with junk orthogonal to (ℂ^{N+1})^{⊗3} ⊗ |0⟩_A; indices i ∈ [N] → oracles 0, 1, 2 with exact amplitude conditions on the zero-ancilla, values-≤-N components of the specified columns; index i : Fin N held as register value i + 1 on ⌈log₂(N+1)⌉ qubits, most significant bit first; reason: equivalent conditions; Lean convention
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §4, Theorem 2, p. 16

import Mathlib
import Definitions.Def_QAlgorithms_Defs_OPIOraclePrograms
import Definitions.Def_QAlgorithms_Defs_OPIUniformity
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_QuadSDE_DriftClass
import Definitions.Def_QuadSDE_Observable
import Definitions.Def_QuadSDE_NoisySDE
import Definitions.Def_QuadSDE_OracleModel
import Definitions.Def_QuadSDE_Instance
import Definitions.Def_QuadSDE_AlgorithmModel

open MeasureTheory ProbabilityTheory QAlgorithms QAlgorithms.OPI
open scoped NNReal

namespace QuadSDE

/-- **Theorem 2 (quantum algorithm for APX-SDE in the oracle model).**
Bravyi, Byrne, Zayats, Zhuk, Zlokapa, *Quantum algorithms for stochastic nonlinear differential
equations*, arXiv:2606.08349 (sha256 29bd9b01…), §4, Theorem 2, p. 16: "There is a quantum
algorithm that takes as input an instance of APX-SDE in the oracle-based input model of Section 3
and outputs a real number `v̂` such that `Pr[|v̂ − E_noise u₀(X(T))| ≤ ϵ] ≥ 2/3` using
`poly(T, log N, J, r, ϵ⁻¹, p⁻¹, q⁻¹) exp(2‖Y‖²/p)` (24) elementary quantum gates and oracle
queries. The algorithm uses `poly(T, log N, J, r, log(ϵ⁻¹), p⁻¹, q⁻¹, ‖Y‖)` (25) qubits, including
ancillas."

There is one uniform family `A` of quantum programs and constants `C, K` such that, for every
instance `x` (dimension `N`, oracle ancilla sizes `a_V, a_P`, channels `r`, strength `J`, noise
rates `p, q`, time `T`, tolerance `ε`, squared norm `‖Y‖²`, observable `u₀`), the program `A x` calls the
three oracles `Val_c, Pos_c, Val_Y` (controlled and inverse calls allowed), and for every hidden
admissible drift `c` with strength `≤ J` and `≤ r` channels, every `Y` with `‖Y‖²` as supplied, every
unitary oracle triple satisfying Eqs. (18)–(20) (junk arbitrary), and every probability space
carrying the noise `(W, Z)` and a solution `X` of Eq. (2) on `[0, T]` with `X(0) = Y + √p Z`:
1. `u₀(X(T))` is integrable;
2. with probability at least `2/3` the program outputs `v̂` with `|v̂ − E u₀(X(T))| ≤ ε`;
3. its charged resources (qubits, classical bits, gates, oracle queries, measurements,
   preparations, classical operations, worst case over branches) are at most
   `C (1 + T + log₂(N+1) + J + r + 1/ε + 1/p + 1/q + a_V + a_P)^K · exp(2‖Y‖²/p)`;
4. its number of qubits is at most
   `C (1 + T + log₂(N+1) + J + r + log₂(1 + 1/ε) + 1/p + 1/q + ‖Y‖ + a_V + a_P)^K`.

**Formalization Note.** "A quantum algorithm" is a `QAlgorithms.OPI.UniformResourceFamily`: one
public classical constructor that, on the binary encoding of the instance, writes the program
(adaptive gates, oracle calls, measurements, coins, classical steps over `{H, T, CNOT}`) within a
polynomial time and space budget in `expansionScale x` (which includes the input length and
`⌈exp(2‖Y‖²/p)⌉`). The constructor never sees `c` or `Y`. `poly(·)` is `C (1 + Σ args)^K` with
`C, K` chosen after the algorithm and before every instance; `log N` is `log₂(N + 1)` and
`log(ϵ⁻¹)` is `log₂(1 + 1/ε)`. The oracle ancilla sizes `a_V, a_P` ("poly(log N) qubits", p. 14) are
inputs and enter both polynomials. The output bits are read as a real number by `decodeReal`; a
failure leaf is never a success. The expectation is the Bochner integral of `u₀(X(T))` over the
probability space; clause 1 makes it genuine. `X` is any pathwise solution (`SolvesPathwise`); with
additive noise and a locally Lipschitz drift it coincides a.s. with the strong solution. Real
inputs are rationals; the norm is supplied as `‖Y‖²`, and `‖Y‖ = √(‖Y‖²)` in the qubit bound. -/
theorem theorem_2 :
    ∃ (A : UniformResourceFamily Instance encodeInstance expansionScale) (C K : ℕ),
      ∀ x : Instance, Interface x (A.construct x) ∧
        ∀ (c : Coeff x.N) (Y : Fin x.N → ℝ), Valid x c Y →
        ∀ O : (k : Fin (A.construct x).oracles) →
            Matrix (Qubits ((A.construct x).arity k)) (Qubits ((A.construct x).arity k)) ℂ,
          OracleTriple x c Y (A.construct x) O →
        ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (B : ℝ≥0 → Ω → Fin x.N → ℝ) (Z : Ω → Fin x.N → ℝ) (X : ℝ≥0 → Ω → Fin x.N → ℝ),
          NoiseSetting P B Z →
          SolvesPathwise P (drift c) (x.q : ℝ) B (fun ω => Y + Real.sqrt (x.p : ℝ) • Z ω) X
            (x.T : ℝ).toNNReal →
          Integrable (fun ω => x.obs.eval (X (x.T : ℝ).toNNReal ω)) P ∧
          membershipOutputLaw (A.construct x).program O
              (fun o => ∃ b, o = some b ∧
                |decodeReal b - ∫ ω, x.obs.eval (X (x.T : ℝ).toNNReal ω) ∂P| ≤ (x.ε : ℝ)) ≥
            2 / 3 ∧
          (membershipResources (A.construct x).program O : ℝ) ≤
            C * (1 + (x.T : ℝ) + Real.logb 2 ((x.N : ℝ) + 1) + (x.J : ℝ) + (x.r : ℝ) +
                1 / (x.ε : ℝ) + 1 / (x.p : ℝ) + 1 / (x.q : ℝ) + (x.aV : ℝ) + (x.aP : ℝ)) ^ K *
              Real.exp (2 * (x.normYsq : ℝ) / (x.p : ℝ)) ∧
          ((A.construct x).qubits : ℝ) ≤
            C * (1 + (x.T : ℝ) + Real.logb 2 ((x.N : ℝ) + 1) + (x.J : ℝ) + (x.r : ℝ) +
                Real.logb 2 (1 + 1 / (x.ε : ℝ)) + 1 / (x.p : ℝ) + 1 / (x.q : ℝ) +
                Real.sqrt (x.normYsq : ℝ) + (x.aV : ℝ) + (x.aP : ℝ)) ^ K := by sorry

end QuadSDE
