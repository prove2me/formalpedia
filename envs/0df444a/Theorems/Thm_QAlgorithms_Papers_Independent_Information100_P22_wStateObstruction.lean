-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_wStateObstruction
-- name    : QAlgorithms.Papers.Independent.Information100.P22.wStateObstruction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:17:38.162092+00:00
-- url     : https://prove2.me/theorems/91307114-5b05-4e3e-9681-910d708e722c
-- title:
--   §V D / Eq.(S73), unnumbered: W-state entanglement and no-go
-- statement:
--   For $m\ge2$, $k\ge1$, take the one-excitation Dicke resource $W_{2mk}$. Across any balanced cut,
--   $$\operatorname{rank}\rho_S=2,\qquad S(\rho_S)=1\text{ bit}.$$
--   Every ordered distinct two-Pauli encoder fails all-output exact recovery. An arbitrary AS unitary leaving $N$ untouched also fails whenever $(m-1)k>1$. The remaining entropy-bound corner $(m,k)=(2,1)$ is still excluded for the prescribed Pauli encoder; no arbitrary-encoder existence claim is made.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 44, §V D / Eq.(S73), unnumbered: W-state entanglement and no-go

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Eq.(S73), PDF pp.15,44: W has exactly one ebit and both stated no-go regimes. -/
theorem wStateObstruction (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k) :
    (rhoS (dickeResource (Wires m k) 1)).rank = 2 ∧
    vnEntropy (rhoS (dickeResource (Wires m k) 1)) = 1 ∧
    (∀ P Q : Axis, P ≠ Q → ¬ AllRecoverable (dickeResource (Wires m k) 1) (twoPauliEncoder m k P Q)) ∧
    (1 < (m-1)*k → ∀ U : Matrix.unitaryGroup (Qubits k × Signals m k) ℂ,
      ¬ AllRecoverable (dickeResource (Wires m k) 1) (U : Op _)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
