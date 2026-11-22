-- Prove2me | Theorems.Thm_RandPurIso_Completion_theorem_4_1
-- name    : RandPurIso.Completion.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:33:05.561991+00:00
-- url     : https://prove2.me/theorems/17f71c78-0de8-4714-a801-85ab90dad295
-- title:
--   Theorem 4.1 — controlled isometry queries from one forward query per call
-- statement:
--   Let $T,M,N\in\mathbb N$ with $N\mid M$. There is a simulator $\mathrm{Sim}_{\mathrm{ctrl}}$ that makes at most one uncontrolled forward query to its oracle per invocation such that for every partial isometry $V:\mathcal H([N])\to\mathcal H([M])$ with $|0\rangle$ in its support and every oracle algorithm $A$ making at most $T$ controlled queries,
--   $$\mathop{\mathbb E}_{\theta\leftarrow[0,2\pi)}\big[A^{\mathrm{ctrl}[e^{i\theta}V]}\big]=A^{\mathrm{Sim}^V_{\mathrm{ctrl}}} .$$
--   Furthermore $\mathrm{Sim}_{\mathrm{ctrl}}$ can be implemented to within error $\varepsilon$ using $\mathrm{poly}(T,\log M,\log(1/\varepsilon))$ gates.
--
--   Formally, $\mathcal H([M])=\mathcal H([N])\otimes\mathcal H([M/N])$ and there are absolute $C,k$ such that for all $T,M,N$ with $N\mid M$ there is one Clifford+T stateful circuit, with at most one query to $\Phi^V$ and at most $C(T+\lceil\log_2M\rceil+2)^k$ instructions, satisfying the identity exactly for every such $V$ and every algorithm. Controlled access to a randomly phased isometry thus reduces to plain forward access.
--
--   Differences from the source:
--   - generalization: a simulator with the exact identity, implementable within error ε with poly(T, log M, log(1/ε)) gates → one exact Clifford+T circuit with ≤ C·(T + ⌈log₂M⌉ + 2)^k instructions satisfying the identity; reason: the nine steps are reversible arithmetic, controlled swaps and one query, exact over Clifford+T; the circuit implements itself with error 0 ≤ ε for every ε
--   - encoding: V : H([N]) → H([M]) = A ⊗ B → V : Fin N → Fin N × Fin (M/N); qubit encodings ctrlFinEncIn/ctrlFinEncOut and isoQueryFin, ⊥ by a flag qubit; reason: the proof's identification H([M]) = A ⊗ B
--   - encoding: E over θ ← [0, 2π); |0⟩ in the support of V → (1/2π)∫₀^{2π}; (V†V)|0⟩ = |0⟩; reason: Definition 3.3's Supp(V)
--   - generalization: A^O := A^O(|0⟩⟨0|_{Out,A}) on the workspace A (Definition 3.2) → any finite workspace W and any initial density matrix of the algorithm (OracleAlg.init); reason: Definition 3.2's "without loss of generality"; |0⟩⟨0| is the special case init = |0⟩⟨0|
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorem 4.1, p. 26

import Mathlib
import Definitions.Def_RandPurIso_Completion_OracleAlg
import Definitions.Def_RandPurIso_Completion_contractionOracle
import Definitions.Def_RandPurIso_Completion_ctrlMap
import Definitions.Def_RandPurIso_Completion_IsContraction
import Definitions.Def_RandPurIso_Completion_StatefulCirc
import Definitions.Def_RandPurIso_Completion_isoQueryFin
open Matrix
open ShiShallow
open MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace RandPurIso.Completion

/-- **Theorem 4.1** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 26).

Let `T, M, N ∈ ℕ` with `N | M`. There is a simulator `Sim_ctrl` that makes at most one uncontrolled
forward query to the oracle per invocation such that for every partial isometry `V : H([N]) → H([M])`
with `|0⟩` in its support and every oracle algorithm `A` making at most `T` controlled queries,
`E_{θ←[0,2π)} [A^{ctrl[e^{iθ}·V]}] = A^{Sim^V_ctrl}`. Furthermore, `Sim_ctrl` can be implemented to
within error `ε` using `poly(T, log M, log(1/ε))` gates.

**Formalization Note.**
* `H([M]) = A ⊗ B` with `A = H([N])`, `B = H([M/N])` (the proof's identification), so `V` is a
  matrix `Fin N × Fin (M/N) ← Fin N`; `ctrl[·]` is Definition 3.9 with `A_pure = B`, used through `Φ`.
* `E_θ` is `(1/2π) ∫_0^{2π}`.
* The simulator is a Clifford+T stateful circuit (`StatefulCirc`) with at most one query to the
  qubit form of `Φ^V` (`isoQueryFin`), chosen before `V` and the algorithm, and it satisfies the
  identity **exactly**, with at most `C (T + ⌈log₂ M⌉ + 2)^k` instructions (`C, k` absolute). This
  implies the "Furthermore" clause for every `ε` (the circuit implements itself with error 0); see
  `Differences from the source`. -/
theorem theorem_4_1 :
    ∃ C k : ℕ, ∀ T M N : ℕ, N ∣ M →
      ∃ S : StatefulCirc 1 (fun _ => Nat.clog 2 N + Nat.clog 2 (M / N) + 1)
          (1 + (Nat.clog 2 N + Nat.clog 2 (M / N) + 1)),
        QInstr.queryCount 0 S.circ ≤ 1 ∧
        (S.circ.length : ℝ) ≤ C * ((T : ℝ) + Nat.clog 2 M + 2) ^ k ∧
        ∀ (V : Matrix (Fin N × Fin (M / N)) (Fin N) ℂ), IsPartialIsometry V →
          (Vᴴ * V).mulVec (fun x => if x.val = 0 then 1 else 0) =
            (fun x => if x.val = 0 then 1 else 0) →
        ∀ (W : Type) [Fintype W] [DecidableEq W]
          (A : OracleAlg (Bool × Fin N) (Option (Bool × (Fin N × Fin (M / N)))) W),
          A.numQueries ≤ T →
          ((1 / (2 * Real.pi) : ℝ) : ℂ) • ∫ θ in (0 : ℝ)..(2 * Real.pi),
              A.run (contractionOracle
                (liftUnit (ctrlMap true (Complex.exp (θ * Complex.I) • V)
                  (idleEmbed (fun b : Fin (M / N) => if b.val = 0 then 1 else 0)))) unitInit) =
            A.run (S.realize (fun _ => isoQueryFin V) ctrlFinEncIn ctrlFinEncOut) := by sorry

end RandPurIso.Completion
