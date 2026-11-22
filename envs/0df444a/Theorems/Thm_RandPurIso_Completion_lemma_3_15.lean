-- Prove2me | Theorems.Thm_RandPurIso_Completion_lemma_3_15
-- name    : RandPurIso.Completion.lemma_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:33:07.093917+00:00
-- url     : https://prove2.me/theorems/f86eaefa-66a4-4238-ae65-bffe7950f18f
-- title:
--   Lemma 3.15 — efficient implementation of $PR_{[N],T}$
-- statement:
--   Let $N,T\in\mathbb N$ and $0<\varepsilon<1$. The channels associated with $PR_{[N],T}$, its adjoint, and their controlled versions can be implemented to within trace-distance error $\varepsilon$, including an arbitrary reference register, using $\mathrm{poly}(T,\log N,\log(1/\varepsilon))$ gates; the same circuits give coherent measurements of the initial-space projector $PR^\dagger PR$ and the range projector $PR\,PR^\dagger$ to the same accuracy with the same gate bound.
--
--   Formally, there are absolute $C,k$ such that for all $N,T$ and $\varepsilon\in(0,1)$, with
--   $$B=C\,\big(T+\lceil\log_2N\rceil+\log_2(1/\varepsilon)+2\big)^k ,$$
--   each of $\Phi_{PR}$, $\Phi_{PR^\dagger}$, $\Phi_{\mathrm{ctrl}[PR]}$, $\Phi_{\mathrm{ctrl}[PR^\dagger]}$, $M^{PR^\dagger PR}$, $M^{PR\,PR^\dagger}$ is implemented within $\varepsilon$ by a Clifford+T circuit with at most $B$ gates in the natural encoding of $\mathcal H([N])\otimes\mathbf{St}$. This is §§4.2.3 and 5.3 of [FLM+26].
--
--   Differences from the source:
--   - encoding: poly(T, log N, log(1/ε)) gates → C·(T + ⌈log₂N⌉ + log₂(1/ε) + 2)^k with C, k absolute, one pair for all six; reason: standard reading of poly; + 2 keeps the base ≥ 2
--   - encoding: registers of unspecified encoding → natural encoding prRegEnc (length register, T input and T output slots of ⌈log₂N⌉ qubits) plus a flag qubit for ⊥; reason: the gate bound is only meaningful for a fixed natural encoding
--   - reading: their controlled versions; coherent measurements of the initial-space and range projectors → Φ of ctrl[PR], ctrl[PR†] (Definition 3.9, square form) and M^{PR†PR}, M^{PR PR†} (Definition 3.8); reason: Definition 3.3: Supp is the image of V†V, Im of VV†
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Lemma 3.15, p. 24

import Mathlib
import Definitions.Def_RandPurIso_Completion_ApproxImpl
import Definitions.Def_RandPurIso_Completion_pathRecording
import Definitions.Def_RandPurIso_Completion_prRegEnc
import Definitions.Def_RandPurIso_Completion_ctrlMap
import Definitions.Def_RandPurIso_Completion_coherentMeasU
open Matrix
open ShiShallow

namespace RandPurIso.Completion

/-- **Lemma 3.15 (efficient implementation, Sections 4.2.3 and 5.3 of [FLM+26])** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 24).

Let `N, T ∈ ℕ` and `0 < ε < 1`. The channels associated with `PR_{[N],T}`, its adjoint, and their
controlled versions can be implemented to within trace-distance error `ε`, including an arbitrary
reference register, using `poly(T, log N, log(1/ε))` gates. The underlying circuits also give
coherent measurements of the initial-space and range projectors to the same accuracy with the same
gate bound.

**Formalization Note.** Six implementations, one gate bound `C (T + ⌈log₂N⌉ + log₂(1/ε) + 2)^k`
with `C, k` absolute: `Φ_{PR}`, `Φ_{PR†}`, `Φ_{ctrl[PR]}`, `Φ_{ctrl[PR†]}` (Definition 3.9, square
form) and the coherent measurements `M^{PR†PR}` (initial space) and `M^{PR PR†}` (range)
(Definition 3.8). Registers use the natural encoding `prRegEnc` (fixed, part of the statement):
`bin x`, then the length of the recording in `⌈log₂(T+1)⌉` qubits and `T` input and `T` output
slots of `⌈log₂N⌉` qubits, plus a flag qubit for `⊥`; control and measurement qubits are added in
front and at the end. See `ApproxImpl`. -/
theorem lemma_3_15 :
    ∃ C k : ℕ, ∀ N T : ℕ, ∀ ε : ℝ, 0 < ε → ε < 1 →
      let B : ℝ := C * ((T : ℝ) + Nat.clog 2 N + Real.logb 2 (1 / ε) + 2) ^ k
      ApproxImpl prRegEnc (pathRecording N T) ε B ∧
      ApproxImpl prRegEnc (pathRecording N T)ᴴ ε B ∧
      ApproxImpl (fun cx : Bool × (Fin N × PRSt N T) => Fin.append (fun _ : Fin 1 => cx.1) (prRegEnc cx.2))
        (ctrlMap true (pathRecording N T) 1) ε B ∧
      ApproxImpl (fun cx : Bool × (Fin N × PRSt N T) => Fin.append (fun _ : Fin 1 => cx.1) (prRegEnc cx.2))
        (ctrlMap true (pathRecording N T)ᴴ 1) ε B ∧
      ApproxImpl (fun xc : (Fin N × PRSt N T) × Bool => Fin.append (prRegEnc xc.1) (fun _ : Fin 1 => xc.2))
        (coherentMeasU ((pathRecording N T)ᴴ * pathRecording N T)) ε B ∧
      ApproxImpl (fun xc : (Fin N × PRSt N T) × Bool => Fin.append (prRegEnc xc.1) (fun _ : Fin 1 => xc.2))
        (coherentMeasU (pathRecording N T * (pathRecording N T)ᴴ)) ε B := by sorry

end RandPurIso.Completion
