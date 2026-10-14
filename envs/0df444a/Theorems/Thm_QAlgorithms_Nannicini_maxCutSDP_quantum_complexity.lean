-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_maxCutSDP_quantum_complexity
-- name    : QAlgorithms.Nannicini.maxCutSDP_quantum_complexity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:54:29.69776+00:00
-- url     : https://prove2.me/theorems/dd1c3588-3147-4b08-a8b8-058b72d5482b
-- title:
--   End-to-end complexity of the quantum MaxCut SDP solver in the QRAM model (corrected statement)
-- statement:
--   This is Proposition 8.34 of Nannicini, the end-to-end cost of the quantum mirror-descent solver for the MaxCut SDP relaxation, stated in an explicit hybrid classical–quantum QRAM cost model.
--
--   Let $n=2^q$. For a nonzero real symmetric $C\in\mathbb R^{n\times n}$ put $\hat C=C/\|C\|_F$. Call a density matrix $\rho\in\mathbb C^{n\times n}$ an $\epsilon$-solution of (MaxCutSDP) if
--
--   $$\sum_{j=1}^n\Big|\rho_{jj}-\frac1n\Big|\le\epsilon\qquad\text{and}\qquad \operatorname{Tr}(\hat C\rho)\ \ge\ \operatorname{Tr}(\hat C\sigma)-\epsilon\ \text{ for every density matrix }\sigma\text{ with }\operatorname{diag}(\sigma)=\tfrac1n\mathbb 1.$$
--
--   A hybrid algorithm consists of (i) a classical preprocessing program, a straight-line program of real arithmetic operations ($+,-,\times,\div,\sqrt\cdot,\arccos,\arg$, rational constants), which is the only part that reads the entries of $C$ and which writes the input half of a QRAM ($U_{\mathrm{QRAM}}|j\rangle|y\rangle=|j\rangle|y\oplus M_j\rangle$, Def. 5.39); (ii) $R$ quantum runs, each applying a circuit of two-qubit gates and QRAM calls to $|0\cdots0\rangle$ and measuring all qubits, where the circuit of each run and the contents of the work half of the QRAM are chosen classically from the outcomes of the earlier runs; (iii) an output, computed from all outcomes, in the form of a list of pairs $(y^{(i)},d^{(i)})\in\mathbb R^2\times\mathbb R^n$, which stands for the matrix
--
--   $$\bar\rho=\frac1{L}\sum_{i=1}^{L}\frac{\exp\big(y^{(i)}_1\hat C+y^{(i)}_2\operatorname{diag}(d^{(i)})\big)}{\operatorname{Tr}\exp\big(y^{(i)}_1\hat C+y^{(i)}_2\operatorname{diag}(d^{(i)})\big)}.$$
--
--   The theorem: there are absolute constants $K>0$ and $c$ such that for all $q$, all $\epsilon\in(0,1]$ and all $\delta\in(0,1)$, with $\Lambda=\log(2+n)+\log(2+1/\epsilon)+\log(2+1/\delta)$, there is a hybrid algorithm, fixed before $C$, such that
--
--   1. the QRAM has size at most $K n^2\Lambda^c$, with words of at most $K\Lambda^c$ bits;
--   2. the preprocessing uses at most $K n^2\Lambda^c$ classical operations;
--   3. along every measurement record the total number of QRAM accesses and additional gates is at most $K\,\dfrac{n^{1.5}}{\epsilon^5}\Lambda^c$;
--   4. for every nonzero real symmetric $C$, with probability at least $1-\delta$ the output $\bar\rho$ is an $\epsilon$-solution of (MaxCutSDP).
--
--   The proposition is the payoff of the chapter's MaxCut analysis: the subgradient estimation of Prop. 8.28, the iteration count of Thm. 8.30 and the Hamiltonian structure of Lem. 8.33 combine into a quantum solver whose quantum cost is sublinear in the $n^2$ entries of $C$.
--
--   **Formalization Note** The printed proposition has no cost model, no success probability, and no precise meaning for the tolerance over the binary search on $\gamma$; these are fixed as above. The classical bookkeeping between quantum runs (tallying samples, forming the subgradients, updating $y$ and $D$) is not counted, matching the proof, which takes the classical cost from Prop. 7.29 alone; that bookkeeping never sees $C$. The output is the source's own representation of the iterate (Rem. 8.27, Lem. 8.33): with an arbitrary decoder, the optimum could be read off $\hat C$ for free.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 204, Proposition 8.34. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_SDP
import Definitions.Def_QAlgorithms_Nannicini_Ch08b_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms.SDP




















/-- Corrected statement. Nannicini p.204, Proposition 8.34, as printed: "Given access to a QRAM
of size `Õ(n²)`, we can determine a solution to (MaxCutSDP) with optimality and feasibility
tolerance `ϵ` (i.e., problem (MaxCutSDP-F)) using `Õ(n^{1.5}/ϵ⁵)` accesses to the QRAM and
additional gates, and `Õ(n²)` classical operations."

What was changed. (1) Cost model (the source has none): a hybrid algorithm, fixed before the
input `C`, consists of a classical preprocessing program `Prog` (straight-line real arithmetic,
`MCPrepOp`) that alone reads `C` and writes the input half of the QRAM, and `R` quantum runs. Run
`k` applies a circuit over two-qubit gates and QRAM calls to `|0⟩` and measures every qubit (the
QRAM holds words of `r = Õ(1)` bits, the `Õ(1)`-bit entries of the Prop. 7.29 data structure: a
unit-cost call reading an `n²`-bit word would let one access read all of `C`); the
circuit and the work half of the QRAM (where `D` is stored) are chosen by a classical controller
from the earlier outcomes only, and the output is a function of all outcomes. "Accesses to the QRAM
and additional gates" is the total number of QRAM calls plus gates along the run, bounded for
every measurement record; "classical operations" is the length of `Prog`. The controller's own
bookkeeping (tallying samples, forming `G^(t)`, updating `y` and `D`) is not counted, as in the
proof, which inherits the classical cost from Prop. 7.29 alone. (2) Success probability: the
source's estimates hold only with high probability; the output is correct with probability
`≥ 1 − δ` for every `δ ∈ (0, 1)`, and `Õ` may hide `polylog(1/δ)`. (3) "Optimality and
feasibility tolerance `ϵ`" is the reading Rem. 8.36 relies on (a solution of (MaxCutSDP)): a
density matrix with `‖diag(ρ) − 𝟙/n‖₁ ≤ ϵ` and `Tr(Ĉρ) ≥ OPT − ϵ` (`IsMaxCutSDPSolution`), so the
`O(log 1/ϵ)` binary-search calls are inside the algorithm and the `Õ`. The other reading, solving
one (MaxCutSDP-F) instance at a given `γ`, is not stated. (4) "Determine a solution": the output is
the source's classical representation of the iterate, a list of `(y, d)` standing for the average
of the Gibbs states of `y_1 Ĉ + y_2 diag(d)` (`mcGibbsMixture`); without a fixed representation any
decoder could compute the optimum from `Ĉ` itself. (5) `n = 2^q`, the case of the components
Props. 7.29, 7.38 (stated for `d = 2^q`, `n = 2^q`), and `ϵ ≤ 1`. (6) `Õ(g)` is `K · g · L^c` with
`L = log(2+n) + log(2+1/ϵ) + log(2+1/δ)` and absolute `K, c` chosen before `q, ϵ, δ` (Def. 1.11).

Why. The printed claim composes components (Props. 7.21, 7.29, 7.38) whose resources are unpinned
as printed, has no cost model for "classical operations", never states the success probability of
"determine", and does not say what tolerance the binary search over `γ` delivers. Without the
word-length bound a single unit-cost QRAM access could read all of `Ĉ`. The standing
assumptions of §8.4 are kept: `C` real symmetric and nonzero (so `Ĉ = C/‖C‖_F` is defined). -/
theorem maxCutSDP_quantum_complexity :
    ∃ K : ℝ, 0 < K ∧ ∃ c : ℕ, ∀ (q : ℕ) (ε δ : ℝ), 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
      ∃ (b r m R : ℕ) (Prog : List MCPrepOp) (addr : Qubits b → ℕ)
        (circ : (k : ℕ) → (Fin k → Qubits m) →
          OracleCircuit twoQubitGateSet (fun _ : Fin 1 => (b + 1) + r) m)
        (dyn : (k : ℕ) → (Fin k → Qubits m) → Qubits b → Qubits r)
        (out : (Fin R → Qubits m) → List ((Fin 2 → ℝ) × (Fin (2 ^ q) → ℝ))),
        (2 : ℝ) ^ (b + 1) * r ≤ K * ((2 : ℝ) ^ q) ^ 2 *
          (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ε) + Real.log (2 + 1 / δ)) ^ c ∧
        (r : ℝ) ≤ K *
          (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ε) + Real.log (2 + 1 / δ)) ^ c ∧
        (Prog.length : ℝ) ≤ K * ((2 : ℝ) ^ q) ^ 2 *
          (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ε) + Real.log (2 + 1 / δ)) ^ c ∧
        (∀ h : Fin R → Qubits m, (mcHistCost circ h : ℝ) ≤
          K * ((2 : ℝ) ^ q * Real.sqrt ((2 : ℝ) ^ q)) / ε ^ 5 *
            (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ε) + Real.log (2 + 1 / δ)) ^ c) ∧
        ∀ C : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℝ, C.IsSymm → C ≠ 0 →
          1 - δ ≤ mcSuccessProb circ dyn (mcStaticWords b r Prog addr C)
            (fun h => IsMaxCutSDPSolution C ε (mcGibbsMixture C (out h))) := by
  sorry

end QAlgorithms.Nannicini
