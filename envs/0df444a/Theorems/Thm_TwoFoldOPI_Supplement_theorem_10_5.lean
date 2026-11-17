-- Prove2me | Theorems.Thm_TwoFoldOPI_Supplement_theorem_10_5
-- name    : TwoFoldOPI.Supplement.theorem_10_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:09:45.376455+00:00
-- url     : https://prove2.me/theorems/02244dc6-8d50-487c-a6b1-0b030ea9ce31
-- title:
--   Theorem 10.5 — efficient preparation of load states
-- statement:
--   Let $\mathcal T=\{x\in[n]^m: c_a(x)\in B_a\ \forall a\in[n]\}$ be nonempty, where each set $B_a\subseteq\{0,\dots,m\}$ of allowed loads is given by its indicator table or by a membership circuit of size $\mathrm{poly}(m,n)$. Then the state
--   $$|\mathcal T\rangle=\frac{1}{\sqrt{|\mathcal T|}}\sum_{x\in\mathcal T}|x\rangle$$
--   can be prepared to trace-distance error $\epsilon$ with $\mathrm{poly}(m,n,\log(1/\epsilon))$ gates, including the construction of the indicator tables.
--
--   Load states are the target states of the histogram-constrained code-intersection problems; this theorem supplies the preparation hypothesis of Regev's reduction for them.
--
--   Differences from the source:
--   - generalization: membership circuits of size poly(m, n) → circuits of any size, with the resource bound P(m + n + t + total circuit size); reason: for circuits of size poly(m, n) the bound is poly(m, n, log(1/ϵ)), so the statement specializes to the source's
--   - encoding: prepared with poly(m, n, log(1/ϵ)) gates, including the construction of the indicator tables → one uniform constructor (QAlgorithms.OPI.UniformResourceFamily, polynomial-time classical construction) produces a pure Clifford+T circuit whose gates plus qubits are at most P(scale), on input t = ⌈log₂(1/ϵ)⌉; reason: the base mission's uniform algorithm model; table construction is part of the polynomial-time construction
--   - reading: the state |T⟩ is prepared to trace-distance error ϵ → the reduced state of the first m⌈log₂ n⌉ qubits (work qubits traced out) is within trace distance ϵ of |T⟩; reason: same preparation convention as the published Theorem 5.30
--   - encoding: circuits that are uniformly constructible in poly(m, n) time → circuits given as input; reason: composing the circuit constructor with the algorithm covers that case
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §10.2, Theorem 10.5, p. 54

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Defs_OPIOraclePrograms
import Definitions.Def_QAlgorithms_Defs_OPIUniformity
import Definitions.Def_TwoFoldOPI_gateCircuit
import Definitions.Def_TwoFoldOPI_Supplement_loadSet
import Definitions.Def_TwoFoldOPI_Supplement_LoadInput
import Definitions.Def_TwoFoldOPI_Supplement_loadState
import Definitions.Def_TwoFoldOPI_Supplement_prefixState

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms QAlgorithms.OPI

/-- **Theorem 10.5 (efficient preparation of load states).**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §10.2, Theorem 10.5, p.54: "For nonempty T given as in Definition 10.2, the state |T⟩ can
be prepared to trace-distance error ϵ with poly(m, n, log(1/ϵ)) gates, including the construction
of the indicator tables."; Definition 10.2, p.53 ("let B_a ⊆ {0, 1, …, m} be given by its
indicator table or by a membership circuit of size poly(m, n)").

There is one uniform constructor `A` (`UniformResourceFamily`, Clifford+T, no oracle) and one
polynomial `P` such that for every input `x = (m, n, B, t)` with well-formed circuits (if given
by circuits), with `T = {y ∈ [n]^m : c_a(y) ∈ B_a ∀ a}` nonempty, and `t = ⌈log₂(1/ϵ)⌉` for some
`ϵ > 0`: the program `A.construct x` is a pure gate circuit `V` on at least `m⌈log₂ n⌉` qubits,
its charged resources are at most `P(scale x)`, and the state of its first `m⌈log₂ n⌉` qubits
after `V|0⟩` (other qubits traced out) is within trace distance `ϵ` of `|T⟩`.

**Formalization Note.** "poly(m, n, log(1/ϵ)) gates, including the construction of the indicator
tables": the classical construction of the circuit (which may evaluate the membership circuits)
runs within the family's polynomial bound, and the circuit's gates and qubits are at most
`P(scale)`, `scale = m + n + t` plus the total size of the membership circuits. For circuits of size
`poly(m, n)` (Definition 10.2) this is `poly(m, n, log(1/ϵ))`. The prepared register is the
first `m⌈log₂ n⌉` wires (layout `loadState`); work wires may stay entangled. -/
theorem theorem_10_5 :
    ∃ A : UniformResourceFamily LoadInput LoadInput.encode LoadInput.scale,
      ∃ P : Polynomial ℕ, ∀ x : LoadInput,
        (∀ C, x.allowed = .inr C → ∀ a, (C a).WellFormed) →
        (loadSet x.m x.n x.allowedLoads).Nonempty →
        ∀ ε : ℝ, 0 < ε → x.t = ⌈Real.logb 2 (1 / ε)⌉₊ →
          (A.construct x).oracles = 0 ∧ x.m * Nat.clog 2 x.n ≤ (A.construct x).qubits ∧
          membershipResources (A.construct x).program (fun _ => 1) ≤ P.eval x.scale ∧
          ∃ V : Circuit htcxGateSet (A.construct x).qubits,
            gateCircuit (A.construct x).program = some V ∧
            traceDistance
              (prefixState (x.m * Nat.clog 2 x.n) (A.construct x).qubits
                (act V.unitary (zeroKet _)))
              (pureDensity (loadState x.m x.n (loadSet x.m x.n x.allowedLoads))) ≤ ε := by sorry

end Supplement

end TwoFoldOPI
