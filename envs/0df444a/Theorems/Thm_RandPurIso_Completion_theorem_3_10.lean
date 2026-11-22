-- Prove2me | Theorems.Thm_RandPurIso_Completion_theorem_3_10
-- name    : RandPurIso.Completion.theorem_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:32:19.845075+00:00
-- url     : https://prove2.me/theorems/ffdd2780-faf5-4d36-ac99-7c7c71ac4a0e
-- title:
--   Theorem 3.10 — $\Phi_W$ from one query to each component
-- statement:
--   Let $\Pi_2$ be a projector on $A$, $\Pi_1$ a projector on $A\otimes A_{\mathrm{pure}}$, and $V_1,V_2:A\to A\otimes A_{\mathrm{pure}}$ partial isometries. Set
--   $$W=\Pi_1V_1\Pi_2+(I_{AA_{\mathrm{pure}}}-\Pi_1)V_2(I_A-\Pi_2).$$
--   Then $\Phi_W$ has an efficient implementation making one ordinary query to each of $M^{\Pi_1}$, $M^{\Pi_2}$ and one query to each of $\Phi^{\mathrm{ctrl}[V_1]}$, $\Phi^{\mathrm{ctrl}[V_2]}$.
--
--   Formally, with $A=\{0,1\}^a$ and $A_{\mathrm{pure}}=\{0,1\}^p$: there is an absolute constant $C$ such that for all $a,p$ there is one Clifford+T circuit, with at most $C(a+p+1)$ instructions and exactly one query to each of the four oracles, whose channel equals $\Phi_W$ for **every** choice of $\Pi_1,\Pi_2,V_1,V_2$.
--
--   The result turns structured contractions into query procedures; Corollary 4.2 and the simulator of Theorem 5.4 are built on it.
--
--   Differences from the source:
--   - reading: efficient implementation → ≤ C·(a + p + 1) Clifford+T instructions plus exactly one query to each oracle, one circuit for all Π1, Π2, V1, V2, C absolute; reason: gate count is the paper's efficiency measure; the five-step procedure is linear in the register size
--   - encoding: arbitrary registers A, A_pure → qubit registers A = {0,1}^a, A_pure = {0,1}^p, oracles in qubit form, ⊥ = strings with the flag qubit set; reason: an arbitrary register is padded into qubits (Π, V extended by zero)
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorem 3.10, p. 19

import Mathlib
import Definitions.Def_RandPurIso_Completion_circChannel
import Definitions.Def_RandPurIso_Completion_contractionChannel
import Definitions.Def_RandPurIso_Completion_IsContraction
import Definitions.Def_RandPurIso_Completion_thm310Oracles
open Matrix
open ShiShallow

namespace RandPurIso.Completion

/-- **Theorem 3.10** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 19).

Let `Π₂` be a projector on `A`, `Π₁` a projector on `A ⊗ A_pure`, and `V₁, V₂ : A → A ⊗ A_pure` partial
isometries; set `W = Π₁V₁Π₂ + (I − Π₁)V₂(I − Π₂)`. Then `Φ_W` has an efficient implementation making
one ordinary query to each of `M^{Π₁}`, `M^{Π₂}` and one query to each of `Φ^{ctrl[V₁]}`,
`Φ^{ctrl[V₂]}`.

**Formalization Note.** Qubit model: `A = {0,1}^a`, `A_pure = {0,1}^p`. One circuit `c` (depending
only on `a, p`) with exactly one query to each of the four oracles (`thm310Oracles`) implements
`Φ_W` exactly for every `Π₁, Π₂, V₁, V₂`. Input `|x⟩` is encoded as `|x, 0^p, 0⟩` on `a + p + 1` data
qubits and `(x, z)` is read from `|x, z, 0⟩`, every string with the last (flag) qubit set reads as
`⊥`. "Efficient" is read as: at most `C (a + p + 1)` instructions for one absolute `C`. -/
theorem theorem_3_10 :
    ∃ C : ℕ, ∀ a p : ℕ, ∃ (anc : ℕ) (c : List (QInstr 4 (thm310Widths a p) (a + p + 1 + anc))),
      (∀ j : Fin 4, QInstr.queryCount j c = 1) ∧ c.length ≤ C * (a + p + 1) ∧
      ∀ (P1 : Matrix (Bits a × Bits p) (Bits a × Bits p) ℂ) (P2 : Matrix (Bits a) (Bits a) ℂ)
        (V1 V2 : Matrix (Bits a × Bits p) (Bits a) ℂ),
        IsProjector P1 → IsProjector P2 → IsPartialIsometry V1 → IsPartialIsometry V2 →
        circChannel c (thm310Oracles P1 P2 V1 V2) (fun x => apEnc x (zeroBits p) false)
            (fun xz => apEnc xz.1 xz.2 false) =
          contractionChannel (P1 * V1 * P2 + (1 - P1) * V2 * (1 - P2)) := by sorry

end RandPurIso.Completion
