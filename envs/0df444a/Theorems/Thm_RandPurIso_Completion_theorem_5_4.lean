-- Prove2me | Theorems.Thm_RandPurIso_Completion_theorem_5_4
-- name    : RandPurIso.Completion.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:31:40.078638+00:00
-- url     : https://prove2.me/theorems/77cfa545-c6a4-4858-b85d-9c3ae11145e8
-- title:
--   Theorem 5.4 — an efficient one-query-per-call simulator emulates $T$ forward queries to a Haar-random completion within $O(T\sqrt{N/(M-T)})$
-- statement:
--   Let $T,M,N\in\mathbb N$ with $1\le N<M$ and $T<M$. There is an efficiently implementable, stateful simulator $\mathrm{Sim}$ that makes at most one query to its oracle per invocation such that for every isometry $V:\mathcal H([N])\to\mathcal H([M])$ and every oracle algorithm $A$ making at most $T$ forward queries,
--   $$\mathrm{TD}\Big(\mathop{\mathbb E}_{U_{M_1}\leftarrow\mathrm{Haar}(\mathcal H(M_1))}\big[A^{\Phi^{D^V_{U_{M_1}}}}\big],\ A^{\mathrm{Sim}^{\Phi^V}}\Big)\le O\Big(T\sqrt{\frac{N}{M-T}}\Big).$$
--
--   Formally: there are absolute constants $C_0$, $C$, $k$ such that for all $T,M,N$ as above there is one Clifford+T stateful circuit $\mathrm{Sim}$ with at most $C(T+\lceil\log_2M\rceil+2)^k$ instructions and qubits and at most one query (to $\Phi^V$ on $\lceil\log_2(M+1)\rceil$ qubits) per invocation, such that for every isometry $V$, every completion $D^V$ of $V$, every finite workspace and every algorithm $A$ with at most $T$ queries, the trace distance above is at most $C_0\,T\sqrt{N/(M-T)}$. The simulator is fixed before $V$, the completion and the algorithm.
--
--   The theorem says that forward queries to a Haar-random unitary completion of an isometry can be emulated efficiently with one query to the isometry itself per call; the paper derives from it lower bounds for unitary and channel tasks (§6).
--
--   Differences from the source:
--   - reading: efficiently implementable stateful simulator → Clifford+T stateful circuit with ≤ C·(T + ⌈log₂M⌉ + 2)^k instructions and ≤ C·(T + ⌈log₂M⌉ + 2)^k qubits, C, k absolute; no uniformity of the circuit family; reason: the paper measures efficiency by gate counts (poly(T, log M), p. 30); the fixed exact gate set and the width bound are the strong choice
--   - encoding: O(T√(N/(M−T))) → C₀·T·√(N/(M−T)) with one absolute C₀ chosen before T, M, N; reason: definition of O(·) uniform in all parameters
--   - generalization: a fixed completion D^V ("Fix any completion") → the bound for every completion D^V; reason: Remark 5.3; the stated case is any one completion
--   - encoding: Sim^{Φ^V} with registers H([M]) → H([M]) in binary on ⌈log₂(M+1)⌉ qubits; Sim's oracle is simQueryChannel V (inputs outside H([N]) fail to ⊥ = bin M); outputs read back with every other string as ⊥; private register starts in |0^s⟩, ancillas |0⟩ traced out each call; reason: qubit model of the simulator; the one-query channel gives no more than Φ^V (p. 30)
--   - generalization: A^O := A^O(|0⟩⟨0|) on workspace A → any finite workspace and any initial density matrix; reason: Definition 3.2's WLOG; |0⟩⟨0| is a special case
--   - encoding: E over U_{M1} ← Haar(H(M1)) → Bochner integral against the Haar probability measure on U(M − N), M1 ≅ [M − N] by x ↦ x − N; reason: the integrand is continuous on a compact group
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorem 5.4, p. 29 (informal: Theorem 1.3, p. 5)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_RandPurIso_Completion_OracleAlg
import Definitions.Def_RandPurIso_Completion_traceDist
import Definitions.Def_RandPurIso_Completion_IsCompletion
import Definitions.Def_RandPurIso_Completion_idealOracle
import Definitions.Def_RandPurIso_Completion_StatefulCirc
import Definitions.Def_RandPurIso_Completion_simQueryChannel
open Matrix
open ShiShallow
open MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace RandPurIso.Completion

/-- **Theorem 5.4** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 29; informal version Theorem 1.3, p. 5).

Let `T, M, N ∈ ℕ` with `1 ≤ N < M` and `T < M`. There is an efficiently implementable, stateful
simulator `Sim` that makes at most one query to its oracle per invocation such that for every
isometry `V : H([N]) → H([M])`, every completion `D^V` of `V` and every oracle algorithm `A` making
at most `T` forward queries,
`TD(E_{U_{M1} ← Haar(H(M1))} [A^{Φ^{D^V_{U_{M1}}}}], A^{Sim^{Φ^V}}) ≤ O(T √(N/(M − T)))`.

**Formalization Note.**
* *Efficiently implementable* (Reading 1): `Sim` is a Clifford+T oracle circuit (`StatefulCirc`)
  whose instruction count and number of qubits are at most `C (T + ⌈log₂ M⌉ + 2)^k`, with `C, k`
  absolute (chosen before `T, M, N`); its only access to `V` is the query channel
  `simQueryChannel V` (`Φ^V` on `⌈log₂(M+1)⌉` qubits, inputs outside `H([N])` fail to `⊥`), used at
  most once per invocation.
* *O(·)* (Reading 2): one absolute constant `C₀`, chosen before `T, M, N`.
* The simulator is chosen before `V`, the completion, the workspace and the algorithm.
* *Every completion* (Reading 3): the bound is asserted for every completion `D^V`
  (p. 29 "Fix any completion"; Remark 5.3).
* Registers (Reading 4): `H([M])` is encoded in binary on `⌈log₂(M+1)⌉` qubits and read back with
  every other string as `⊥`; the private register starts in `|0^s⟩` and ancillas are traced out after
  each call (Reading 5). The algorithm's workspace is any finite type and its initial state any
  density matrix (Reading 6).
* `E_U` is the Bochner integral against the Haar probability measure on `U(M − N)`
  (`QAlgorithms.Schur.unitaryHaar`), `U(H(M1))` through `x ↦ x − N`; the integrand is continuous. -/
theorem theorem_5_4 :
    ∃ C₀ : ℝ, ∃ C k : ℕ, ∀ T M N : ℕ, 1 ≤ N → N < M → T < M →
      ∃ S : StatefulCirc 1 (fun _ => qw M) (qw M),
        QInstr.queryCount 0 S.circ ≤ 1 ∧
        (S.circ.length : ℝ) ≤ C * ((T : ℝ) + Nat.clog 2 M + 2) ^ k ∧
        (S.width : ℝ) ≤ C * ((T : ℝ) + Nat.clog 2 M + 2) ^ k ∧
        ∀ (V : Matrix (Fin M) (Fin N) ℂ), Vᴴ * V = 1 →
        ∀ (D : Matrix.unitaryGroup (Fin M) ℂ), IsCompletion V D →
        ∀ (W : Type) [Fintype W] [DecidableEq W] (A : OracleAlg (Fin M) (Option (Fin M)) W),
          A.numQueries ≤ T →
          traceDist
            (∫ U, A.run (idealOracle (N := N) D U) ∂(QAlgorithms.Schur.unitaryHaar (M - N)))
            (A.run (S.realize (fun _ => simQueryChannel V) (fun x => binEnc (qw M) x.val)
              (fun y => binEnc (qw M) y.val)))
            ≤ C₀ * T * Real.sqrt ((N : ℝ) / ((M : ℝ) - T)) := by sorry

end RandPurIso.Completion
