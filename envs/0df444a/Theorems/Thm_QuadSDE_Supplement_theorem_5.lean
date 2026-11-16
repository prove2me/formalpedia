-- Prove2me | Theorems.Thm_QuadSDE_Supplement_theorem_5
-- name    : QuadSDE.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:14:42.321333+00:00
-- url     : https://prove2.me/theorems/5cc4e07d-6059-4c58-bb4b-fba1ab169623
-- title:
--   Theorem 5 — BQP-hardness of APX-SDE: poly-time map $U\mapsto$ instance with $N=1+4\ell2^n$, $p=q=\Theta(1/\log\ell)$ and $\mathbb E\,u_0(X(1))=\alpha+\beta p_U$
-- statement:
--   Consider quantum circuits $U$ on $n\ge1$ qubits made of $\ell\ge16$ gates, each a Toffoli gate, a pair of Hadamard gates $H\otimes H$ on two distinct qubits, or an identity gate, with acceptance probability $p_U=\langle0^n|U^\dagger(|0\rangle\langle0|_{\mathrm{out}}\otimes I)U|0^n\rangle$, the output qubit being the first one.
--
--   There is a polynomial-time classical algorithm and there are universal constants $c_\beta,c_p,C_p,c_\epsilon>0$ such that, on input $U$, the algorithm outputs real numbers $\alpha,\beta$ (to any requested precision $2^{-k}$, $k$ given in unary) and a succinct instance of APX-SDE with
--   $$N=1+4\ell2^n,\qquad Y=(1,1,0,\dots,0),\qquad u_0(x)=x_2,\qquad T=1,$$
--   drift strength $J\le3\ell$, sparsity $s\le16$ and noise rates $p=q$ with $c_p/\log\ell\le p\le C_p/\log\ell$, whose circuits specify $Y$ and an admissible quadratic drift with these parameters, such that:
--   1. $\beta\ge c_\beta\sqrt{\log\ell}/\ell$;
--   2. for every solution $X$ of $dX=f(X)\,dt+\sqrt q\,dW$, $X(0)=Y+\sqrt p\,Z$, on $[0,1]$, $u_0(X(1))$ is integrable and
--   $$\mathbb E_{\mathrm{noise}}u_0(X(1))=\alpha+\beta p_U\qquad(89);$$
--   3. any estimates $\hat v,\hat\alpha,\hat\beta$ within $c_\epsilon/\ell$ of $\mathbb E_{\mathrm{noise}}u_0(X(1)),\alpha,\beta$ give $|(\hat v-\hat\alpha)/\hat\beta-p_U|\le1/12$.
--
--   Thus estimating the expected value with tolerance $\epsilon=\Theta(1/\ell)$ recovers $p_U$ to a fixed constant error, so APX-SDE is BQP-hard (Theorem 1(ii)), already for $\|Y\|=\sqrt2$, $p,q=\Omega(1/\log\log N)$ and $\epsilon=1/\mathrm{poly}(\log N)$.
--
--   Differences from the source:
--   - reading: a classical algorithm running in time poly(n) → a function on bit strings that is CookPvsNP.PolyTimeComputable (Turing machine, time polynomial in the input length), the input being n in unary, then ℓ and the gates in binary, for every circuit (no bound ℓ ≤ poly(n) assumed); reason: reading S3; the input length lies between max(n, ℓ) and O((n + ℓ) log n), so for the source's circuits (ℓ ≤ poly(n)) polynomial in it is poly(n)
--   - reading: outputs a binary representation of real numbers α, β → on input U and a precision k in unary, outputs the instance (independent of k) and rationals α̃_k, β̃_k with |α̃_k − α|, |β̃_k − β| ≤ 2^{−k}; reason: reading S2; α, β are generally irrational; Lemma 10 computes them to additive error δ in time poly(L, log δ⁻¹) and the proof computes them "to the same additive accuracy"
--   - reading: β = Ω(√(log ℓ)/ℓ), p = q = Θ(1/log ℓ), ϵ = Θ(1/ℓ) → universal constants c_β, c_p, C_p, c_ε > 0 fixed before the circuit; natural logarithms; reason: standard reading of the asymptotic notation; p. 36 fixes natural logarithms
--   - reading: suffices to recover p_U with a fixed constant additive error → estimates of E u₀(X(1)), α and β within c_ε/ℓ give (v̂ − α̂)/β̂ within 1/12 of p_U; reason: the proof (p. 39) recovers p_U = (v − α)/β with error 3/255 < 1/12
--   - encoding: an instance of APX-SDE → a succinct-model record (N, s, r, J, T, value bit length, u₀, circuits DriftRow, InitSign, InitPrefix, p, q) written as a bit string, whose circuits specify c and Y exactly, with admissible scalars (J > 0, r, s ≥ 1, 0 < p, q ≤ 1); the error tolerance is not part of the record; reason: §3.1 is the format the proof verifies (p. 39); clause 3 states the tolerance
--   - encoding: indices 1, …, N; u₀(x) = x₂ → Fin N, 0-based: u₀ = Observable.lin 1, Y₀ = Y₁ = 1; circuit inputs carry the 1-based index in binary; reason: Lean convention; same instances
--   - reading: a quantum circuit U as above → n ≥ 1 qubits; gates Toffoli (three distinct qubits), H ⊗ H (two distinct qubits) or identity; ℓ ≥ 16 as a hypothesis; output qubit the first one; reason: the class described on p. 33
--   - generalization: X(t) solves the SDE Eq. (2) → any process X on any probability space carrying (W, Z) that solves Eq. (2) pathwise on [0, 1]; reason: with additive noise and a locally Lipschitz drift every pathwise solution agrees a.s. with the strong solution, so the statement specializes to the source's
--   - encoding: E_noise u₀(X(1)) → Bochner integral with an explicit integrability conclusion; reason: rules out the junk value 0 of a non-integrable integral
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §5, Theorem 5, p. 33

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_QuadSDE_DriftClass
import Definitions.Def_QuadSDE_Observable
import Definitions.Def_QuadSDE_NoisySDE
import Definitions.Def_QuadSDE_Supplement_Circuits
import Definitions.Def_QuadSDE_Supplement_Succinct

open MeasureTheory ProbabilityTheory QAlgorithms.Complexity QAlgorithms.LocalHamiltonian
open scoped NNReal

namespace QuadSDE.Supplement

/-- **Theorem 5 (BQP-hardness of APX-SDE).**
Bravyi, Byrne, Zayats, Zhuk, Zlokapa, *Quantum algorithms for stochastic nonlinear differential
equations*, arXiv:2606.08349 (sha256 29bd9b01…), §5, Theorem 5, p. 33: "There is a classical
algorithm running in time `poly(n)` that takes as input a quantum circuit `U` as above and outputs a
binary representation of real numbers `α, β` with `β = Ω(√(log ℓ)/ℓ)` and an instance of APX-SDE
with `N = 1 + 4ℓ2ⁿ`, `Y = (1, 1, 0, …, 0)`, `u₀(x) = x₂`, `T = 1`. The instance has drift strength
`J ≤ 3ℓ`, drift sparsity `s ≤ 16`, and noise rates `p = q = Θ(1/log ℓ)`. The expected value of the
observable satisfies `E_noise u₀(X(1)) = α + β p_U`. (89) Thus estimating the expected value with an
error tolerance `ϵ = Θ(1/ℓ)` suffices to recover `p_U` with a fixed constant additive error."

There are maps `U ↦ (instance, α, β)`, a polynomial-time computable string function `F`, and
universal constants `c_β, c_p, C_p, c_ε > 0` such that for every circuit `U` of Toffoli, paired
Hadamard and identity gates on `n ≥ 1` qubits with `ℓ ≥ 16` gates:
1. on input `U` and a precision `k` in unary, `F` outputs the succinct APX-SDE instance (the same for
   every `k`) and rationals `α̃_k, β̃_k` with `|α̃_k − α| ≤ 2^{−k}`, `|β̃_k − β| ≤ 2^{−k}`;
2. `β ≥ c_β √(log ℓ)/ℓ`;
3. the instance has `N = 1 + 4ℓ2ⁿ`, `u₀(x) = x₂`, `T = 1`, `J ≤ 3ℓ`, `s ≤ 16`, `p = q` with
   `c_p/log ℓ ≤ p ≤ C_p/log ℓ`, and admissible parameters (`J > 0`, `r, s ≥ 1`, `0 < p, q ≤ 1`);
4. its circuits specify `Y = (1, 1, 0, …, 0)` and an admissible drift `c` with strength `≤ J`,
   sparsity `≤ s` and `≤ r` channels;
5. for every probability space carrying the noise `(W, Z)` and every solution `X` of Eq. (2) on
   `[0, 1]` with `X(0) = Y + √p Z`: `u₀(X(1))` is integrable, `E u₀(X(1)) = α + β p_U` (Eq. (89)), and
   any `v̂, α̂, β̂` within `c_ε/ℓ` of `E u₀(X(1)), α, β` give `|(v̂ − α̂)/β̂ − p_U| ≤ 1/12`.

**Formalization Note.** "Running in time `poly(n)`" is `CookPvsNP.PolyTimeComputable` in the input
length; for the circuits of the source (`ℓ ≤ poly(n)`) the two agree. The reals `α, β` are output
as rational approximations to any precision `2^{−k}`, `k` given in unary (Lemma 10, p. 36: computable
"to additive error `δ` … in time `poly(L, log(δ⁻¹))`"). `Ω` and `Θ` are universal constants chosen
before the circuit; logarithms are natural (p. 36). The "fixed constant additive error" is the
proof's `1/12` (p. 39). Indices are 0-based: `x₂` is `Observable.lin 1` and `Y` has `Y₀ = Y₁ = 1`.
`p_U` projects the first qubit onto `|0⟩`. The expectation is the Bochner integral, with
integrability stated. -/
theorem theorem_5 :
    ∃ (inst : THCircuit → SuccinctSDE) (α β : THCircuit → ℝ) (apx : THCircuit → ℕ → ℚ × ℚ)
      (F : List Bool → List Bool) (cβ cp Cp cε : ℝ),
      CookPvsNP.PolyTimeComputable F ∧ 0 < cβ ∧ 0 < cp ∧ 0 < Cp ∧ 0 < cε ∧
      ∀ U : THCircuit, 16 ≤ U.gates.length →
        (∀ k : ℕ, F (U.encode ++ encNat k) =
          (inst U).encode ++ encRat (apx U k).1 ++ encRat (apx U k).2) ∧
        (∀ k : ℕ, |((apx U k).1 : ℝ) - α U| ≤ ((1 : ℝ) / 2) ^ k ∧
          |((apx U k).2 : ℝ) - β U| ≤ ((1 : ℝ) / 2) ^ k) ∧
        cβ * Real.sqrt (Real.log U.gates.length) / U.gates.length ≤ β U ∧
        (inst U).N = 1 + 4 * U.gates.length * 2 ^ U.n ∧
        (∃ h : 1 < (inst U).N, (inst U).obs = Observable.lin ⟨1, h⟩) ∧
        (inst U).T = 1 ∧
        ((inst U).J : ℝ) ≤ 3 * U.gates.length ∧
        (inst U).s ≤ 16 ∧
        (inst U).p = (inst U).q ∧
        cp / Real.log U.gates.length ≤ ((inst U).p : ℝ) ∧
        ((inst U).p : ℝ) ≤ Cp / Real.log U.gates.length ∧
        (inst U).ParamsValid ∧
        ∃ c : Coeff (inst U).N,
          (inst U).Specifies c (fun i => if i.val < 2 then 1 else 0) ∧
          (inst U).DriftValid c ∧
          ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (B : ℝ≥0 → Ω → Fin (inst U).N → ℝ) (Z : Ω → Fin (inst U).N → ℝ)
            (X : ℝ≥0 → Ω → Fin (inst U).N → ℝ),
            NoiseSetting P B Z →
            SolvesPathwise P (drift c) ((inst U).q : ℝ) B
              (fun ω => (fun i : Fin (inst U).N => if i.val < 2 then (1 : ℝ) else 0) +
                Real.sqrt ((inst U).p : ℝ) • Z ω) X ((inst U).T : ℝ).toNNReal →
            Integrable (fun ω => (inst U).obs.eval (X ((inst U).T : ℝ).toNNReal ω)) P ∧
            ∫ ω, (inst U).obs.eval (X ((inst U).T : ℝ).toNNReal ω) ∂P =
              α U + β U * U.acceptProb ∧
            ∀ v α' β' : ℝ,
              |v - ∫ ω, (inst U).obs.eval (X ((inst U).T : ℝ).toNNReal ω) ∂P| ≤
                cε / U.gates.length →
              |α' - α U| ≤ cε / U.gates.length →
              |β' - β U| ≤ cε / U.gates.length →
              |(v - α') / β' - U.acceptProb| ≤ 1 / 12 := by sorry

end QuadSDE.Supplement
