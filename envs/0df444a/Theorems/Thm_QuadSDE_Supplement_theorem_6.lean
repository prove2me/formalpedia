-- Prove2me | Theorems.Thm_QuadSDE_Supplement_theorem_6
-- name    : QuadSDE.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:15:37.040222+00:00
-- url     : https://prove2.me/theorems/27f62c56-b7da-4a53-80b0-ab7aea047147
-- title:
--   Theorem 6 — PP-hardness of APX-ODE: poly-time map from majority to instances with $N=O(n2^n)$, $T=O((\log N)^2)$ and $u_0(X(T))\ge\frac12$ / $\le-\frac12$
-- statement:
--   The majority problem takes a Boolean function $F:\{0,1\}^n\to\{0,1\}$, $n\ge1$, given by a classical circuit, and asks whether $\sum_xF(x)>2^{n-1}$ (YES) or $\sum_xF(x)\le2^{n-1}$ (NO).
--
--   There is a polynomial-time classical algorithm and there are universal constants $C>0$, $K$ such that, on input $(n,F)$, the algorithm outputs a succinct instance of APX-ODE with
--   $$N\le Cn2^n,\qquad u_0(x)=x_5,\qquad J\le\tfrac32,\qquad s\le16,\qquad T\le C(\log N)^2\qquad(110),$$
--   whose circuits have at most $C(\log N+|F|)^K$ gates ($|F|$ the size of the input circuit) and specify an initial condition $Y$ with exactly four nonzero entries, all equal to one (so $\|Y\|=2$), and an admissible quadratic drift $c$ with these parameters all of whose coefficients $c_{ijk}$ are dyadic rationals with $b\le C\log\log N$ bits, such that the ODE $dX/dt=f(X)$, $X(0)=Y$, has a solution on $[0,T]$ and every such solution satisfies
--   $$u_0(X(T))\ge\tfrac12\ \text{for YES-instances},\qquad u_0(X(T))\le-\tfrac12\ \text{for NO-instances}.$$
--   In particular, any estimate $\hat v$ with $|\hat v-u_0(X(T))|\le\epsilon<\frac12$ is positive exactly on YES-instances.
--
--   Since the majority problem is PP-complete, APX-ODE is PP-hard (Theorem 1(iii)), already for $\|Y\|=O(1)$, $T\le\mathrm{poly}(\log N)$ and constant tolerance, in contrast with the noisy problem.
--
--   Differences from the source:
--   - reading: a classical algorithm running in time poly(n) → a function on bit strings that is CookPvsNP.PolyTimeComputable (Turing machine, time polynomial in the input length); reason: reading S3; the input circuit has size poly(n) (p. 39), so the two agree
--   - reading: O(n2ⁿ), O((log N)²), O(log log N) bits, poly(log N) → universal constants C, K fixed before the input; natural logarithms; reason: standard reading of the asymptotic notation
--   - generalization: circuits specifying c and Y have size poly(log N), for majority instances given by circuits of size poly(n) → at most C (log N + |F_c|)^K gates for every input circuit F_c; reason: the output circuits must evaluate the input circuit; for |F_c| ≤ poly(n), since log N ≥ n log 2, this is the source's poly(log N)
--   - encoding: an instance of the majority problem with an n-bit Boolean function → n ≥ 1 and a well-formed QAlgorithms.BoolCircuit n 1 (AND/OR/NOT), written as n in unary followed by the circuit in self-delimiting binary; reason: the source fixes no gate basis; n ≥ 1 is p. 40's assumption; n in unary makes the input length at least n, so polynomial time in it is the source's poly(n)
--   - encoding: an instance of APX-ODE → a succinct-model record whose circuits specify c and Y exactly, with admissible scalars (J > 0, r, s ≥ 1, T ≥ 0); the error tolerance is not part of the record; indices 0-based, u₀ = Observable.lin 4; reason: §3.1 is the format the proof verifies (p. 46); Lean convention
--   - encoding: X(t) solves the ODE (1) → integral form on [0, T]; a solution exists and every solution satisfies the bounds; reason: the ODE has a unique solution (p. 45); the existence clause keeps the statement from being vacuous
--   - reading: any error tolerance ϵ < 1/2 suffices to determine the majority problem answer → every v̂ with |v̂ − u₀(X(T))| ≤ ε < 1/2 is positive iff the instance is YES; reason: p. 45 ("determines the sign of u₀(X(T))")
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §6, Theorem 6 and footnote 4, p. 39

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QuadSDE_DriftClass
import Definitions.Def_QuadSDE_Observable
import Definitions.Def_QuadSDE_Supplement_Succinct
import Definitions.Def_QuadSDE_Supplement_ODE

open QAlgorithms QAlgorithms.Complexity QAlgorithms.LocalHamiltonian

namespace QuadSDE.Supplement

/-- **Theorem 6 (PP-hardness of APX-ODE).**
Bravyi, Byrne, Zayats, Zhuk, Zlokapa, *Quantum algorithms for stochastic nonlinear differential
equations*, arXiv:2606.08349 (sha256 29bd9b01…), §6, Theorem 6, p. 39: "There is a classical
algorithm running in time `poly(n)` that takes as input an instance of the majority problem with an
`n`-bit Boolean function and outputs an instance of APX-ODE with dimension `N = O(n2ⁿ)` and a linear
observable `u₀(x) = x₅` such that `u₀(X(T)) ≥ 1/2` for YES-instances and `u₀(X(T)) ≤ −1/2` for
NO-instances of the majority problem. The APX-ODE has parameters `J ≤ 3/2`, `s ≤ 16`, `‖Y‖ = 2`,
`T = O((log N)²)`. (110) Any error tolerance `ϵ < 1/2` suffices to determine the majority problem
answer. The initial condition `Y` has four nonzero entries, all equal to one. All drift coefficients
`c_ijk` are dyadic rationals with `O(log log N)` bits. The classical circuits specifying the drift
tensor `c` and the initial condition `Y` have size `poly(log N)`."

There are a map from majority instances to succinct APX-ODE instances, a polynomial-time computable
string function `F` and universal constants `C > 0`, `K` such that for every `n ≥ 1` and every
well-formed Boolean circuit `F_c` with `n` inputs and one output (computing `F : {0,1}ⁿ → {0,1}`):
1. `F` maps the code of `(n, F_c)` to the code of the instance;
2. `N ≤ C n 2ⁿ`, `u₀(x) = x₅`, `J ≤ 3/2`, `s ≤ 16`, `T ≤ C (log N)²`, admissible parameters, and the
   three circuits have at most `C (log N + |F_c|)^K` gates, `|F_c|` the size of the input circuit;
3. the circuits specify `Y` and an admissible drift `c` with strength `≤ J`, sparsity `≤ s` and
   `≤ r` channels; `Y` has exactly four nonzero entries, all equal to `1`, and `‖Y‖ = 2`; every
   `c_ijk` is a dyadic rational with `b` bits for some `b ≤ C log log N`;
4. the ODE `dX/dt = f(X)`, `X(0) = Y`, has a solution on `[0, T]`, and every solution satisfies
   `u₀(X(T)) ≥ 1/2` if `Σ_x F(x) > 2^{n−1}` (YES) and `u₀(X(T)) ≤ −1/2` if `Σ_x F(x) ≤ 2^{n−1}` (NO);
   any `v̂` within `ε < 1/2` of `u₀(X(T))` is positive exactly on YES-instances.

**Formalization Note.** "Running in time `poly(n)`" is `CookPvsNP.PolyTimeComputable` in the input
length; the input circuit has size `poly(n)` (p. 39), so the two agree. `O(·)` and `poly(·)` are
universal constants `C, K` chosen before the input; logarithms are natural. The circuit-size bound
`C (log N + |F_c|)^K` holds for every input circuit; for the source's inputs (`|F_c| ≤ poly(n)`, and
`log N ≥ n log 2`) it is the source's `poly(log N)`. "Dyadic rational with
`b` bits" is footnote 4 (`IsDyadicBits`). The majority function is given by a well-formed
`QAlgorithms.BoolCircuit n 1`; `n ≥ 1` as on p. 40. The input is `n` in unary (`encNat`, so the
input length is at least `n`, as for a function `{0,1}ⁿ → {0,1}` whose circuit reads `n` inputs)
followed by the circuit's code; polynomial time in that length is the source's `poly(n)`. Indices are 0-based: `x₅` is `Observable.lin 4`.
The ODE solution is in integral form on `[0, T]`. -/
theorem theorem_6 :
    ∃ (inst : (n : ℕ) → BoolCircuit n 1 → SuccinctODE) (F : List Bool → List Bool) (C : ℝ)
      (K : ℕ),
      CookPvsNP.PolyTimeComputable F ∧ 0 < C ∧
      ∀ (n : ℕ) (Fc : BoolCircuit n 1), 1 ≤ n → Fc.WellFormed →
        F (encNat n ++ encodeBoolCircuit Fc) = (inst n Fc).encode ∧
        ((inst n Fc).N : ℝ) ≤ C * n * 2 ^ n ∧
        (∃ h : 4 < (inst n Fc).N, (inst n Fc).obs = Observable.lin ⟨4, h⟩) ∧
        (inst n Fc).J ≤ 3 / 2 ∧
        (inst n Fc).s ≤ 16 ∧
        ((inst n Fc).T : ℝ) ≤ C * Real.log (inst n Fc).N ^ 2 ∧
        (inst n Fc).ParamsValid ∧
        ((inst n Fc).driftRow.size : ℝ) ≤ C * (Real.log (inst n Fc).N + Fc.size) ^ K ∧
        ((inst n Fc).initSign.size : ℝ) ≤ C * (Real.log (inst n Fc).N + Fc.size) ^ K ∧
        ((inst n Fc).initPrefix.size : ℝ) ≤ C * (Real.log (inst n Fc).N + Fc.size) ^ K ∧
        ∃ (c : Coeff (inst n Fc).N) (Y : Fin (inst n Fc).N → ℝ),
          (inst n Fc).Specifies c Y ∧
          (inst n Fc).DriftValid c ∧
          (Finset.univ.filter fun i => Y i ≠ 0).card = 4 ∧
          (∀ i, Y i ≠ 0 → Y i = 1) ∧
          Real.sqrt (∑ i, Y i ^ 2) = 2 ∧
          (∃ b : ℕ, (b : ℝ) ≤ C * Real.log (Real.log (inst n Fc).N) ∧
            ∀ i j k, IsDyadicBits (c i j k) b) ∧
          (∃ X : ℝ → Fin (inst n Fc).N → ℝ, IsODESol (drift c) Y ((inst n Fc).T : ℝ) X) ∧
          ∀ X : ℝ → Fin (inst n Fc).N → ℝ, IsODESol (drift c) Y ((inst n Fc).T : ℝ) X →
            (2 ^ (n - 1) < acceptCount Fc →
              1 / 2 ≤ (inst n Fc).obs.eval (X ((inst n Fc).T : ℝ))) ∧
            (acceptCount Fc ≤ 2 ^ (n - 1) →
              (inst n Fc).obs.eval (X ((inst n Fc).T : ℝ)) ≤ -1 / 2) ∧
            ∀ ε v : ℝ, ε < 1 / 2 → |v - (inst n Fc).obs.eval (X ((inst n Fc).T : ℝ))| ≤ ε →
              (0 < v ↔ 2 ^ (n - 1) < acceptCount Fc) := by sorry

end QuadSDE.Supplement
