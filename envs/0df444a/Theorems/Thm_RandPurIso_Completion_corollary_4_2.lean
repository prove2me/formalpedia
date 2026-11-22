-- Prove2me | Theorems.Thm_RandPurIso_Completion_corollary_4_2
-- name    : RandPurIso.Completion.corollary_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:32:58.496774+00:00
-- url     : https://prove2.me/theorems/a9ae27e1-f5b1-4b56-9388-d4c5ac4d2e54
-- title:
--   Corollary 4.2 — the contraction simulator
-- statement:
--   Let $\Pi_1,\Pi_2$ be projectors and $V_1,V_2$ partial isometries from $A_{\mathrm{in}}$ to $A_{\mathrm{out}}$ with $|0\rangle$ in the support of $V_1$, and
--   $$W_\theta=e^{i\theta}\Pi_1V_1\Pi_2+(I-\Pi_1)V_2(I-\Pi_2).$$
--   Then there is a simulator $\mathrm{Sim}_{t,\mathrm{contract},W}$ making one ordinary query to each of $M^{\Pi_1}$, $M^{\Pi_2}$, $\Phi^{V_1}$ and one query to $\Phi^{\mathrm{ctrl}[V_2]}$ per invocation such that every oracle algorithm $A$ making at most $t$ queries satisfies
--   $$\mathop{\mathbb E}_{\theta\leftarrow[0,2\pi)}\big[A^{\Phi^{W_\theta}}\big]=A^{\mathrm{Sim}} .$$
--
--   Formally, in the qubit model $A_{\mathrm{in}}=\{0,1\}^a$, $A_{\mathrm{out}}=A_{\mathrm{in}}\otimes\{0,1\}^p$, the simulator is one Clifford+T stateful circuit chosen before $\Pi_1,\Pi_2,V_1,V_2$ and the algorithm. Theorem 5.4's simulator is this corollary applied to $W_f$.
--
--   Differences from the source:
--   - reading: V1, V2 send A_in to A_out → A_out = A_in ⊗ A_pure; reason: ctrl[V2] (Definition 3.9) is defined only for maps A → A ⊗ A_pure; the use on p. 30 has this shape
--   - generalization: a simulator (class unspecified) → a Clifford+T stateful circuit; reason: existence within a smaller class of simulators is a stronger statement; it specializes to the source's
--   - encoding: arbitrary registers; E over θ; |0⟩ → qubit registers {0,1}^a, {0,1}^p with a flag qubit for ⊥; (1/2π)∫₀^{2π}; |0⟩ = |0^a⟩; reason: arbitrary registers pad into qubits
--   - generalization: A^O := A^O(|0⟩⟨0|_{Out,A}) on the workspace A (Definition 3.2) → any finite workspace W and any initial density matrix of the algorithm (OracleAlg.init); reason: Definition 3.2's "without loss of generality"; |0⟩⟨0| is the special case init = |0⟩⟨0|
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Corollary 4.2, p. 28

import Mathlib
import Definitions.Def_RandPurIso_Completion_OracleAlg
import Definitions.Def_RandPurIso_Completion_contractionOracle
import Definitions.Def_RandPurIso_Completion_IsContraction
import Definitions.Def_RandPurIso_Completion_StatefulCirc
import Definitions.Def_RandPurIso_Completion_cor42Oracles
open Matrix
open ShiShallow
open MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace RandPurIso.Completion

/-- **Corollary 4.2** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 28).

Let `Π₁, Π₂` be projectors and `V₁, V₂` partial isometries from `A_in` to `A_out` (with `|0⟩` in the
support of `V₁`), and `W_θ = e^{iθ}Π₁V₁Π₂ + (I − Π₁)V₂(I − Π₂)`. Then there is a simulator
`Sim_{t,contract,W}` making one ordinary query to each of `M^{Π₁}`, `M^{Π₂}`, `Φ^{V₁}` and one query to
the controlled oracle `Φ^{ctrl[V₂]}` such that for all oracle algorithms `A` making at most `t`
queries, `E_{θ←[0,2π)} [A^{Φ^{W_θ}}] = A^{Sim}`.

**Formalization Note.** Qubit model `A_in = A = {0,1}^a`, `A_out = A ⊗ A_pure`, `A_pure = {0,1}^p`
(the shape for which `ctrl[V₂]` of Definition 3.9 is defined, as in Theorem 3.10); `Π₁` acts on
`A_out`, `Π₂` on `A_in`. The simulator is a Clifford+T stateful circuit (`StatefulCirc`) with
exactly one query to each oracle of `cor42Oracles` per invocation, chosen before `Π₁, Π₂, V₁, V₂`
and the algorithm; `|0⟩` is `|0^a⟩`. The input `|x⟩` is encoded as `|x, 0^p, 0⟩`, outputs `(x, z)` are
read from `|x, z, 0⟩` and every string with the flag qubit set reads as `⊥`. -/
theorem corollary_4_2 (t : ℕ) :
    ∀ a p : ℕ, ∃ S : StatefulCirc 4 (cor42Widths a p) (a + p + 1),
      (∀ j : Fin 4, QInstr.queryCount j S.circ = 1) ∧
      ∀ (P1 : Matrix (Bits a × Bits p) (Bits a × Bits p) ℂ) (P2 : Matrix (Bits a) (Bits a) ℂ)
        (V1 V2 : Matrix (Bits a × Bits p) (Bits a) ℂ),
        IsProjector P1 → IsProjector P2 → IsPartialIsometry V1 → IsPartialIsometry V2 →
        (V1ᴴ * V1).mulVec (fun x => if x = zeroBits a then 1 else 0) =
          (fun x => if x = zeroBits a then 1 else 0) →
        ∀ (W : Type) [Fintype W] [DecidableEq W]
          (A : OracleAlg (Bits a) (Option (Bits a × Bits p)) W), A.numQueries ≤ t →
          ((1 / (2 * Real.pi) : ℝ) : ℂ) • ∫ θ in (0 : ℝ)..(2 * Real.pi),
              A.run (contractionOracle
                (liftUnit (Complex.exp (θ * Complex.I) • (P1 * V1 * P2) + (1 - P1) * V2 * (1 - P2)))
                unitInit) =
            A.run (S.realize (cor42Oracles P1 P2 V1 V2) (fun x => apEnc x (zeroBits p) false)
              (fun xz => apEnc xz.1 xz.2 false)) := by sorry

end RandPurIso.Completion
