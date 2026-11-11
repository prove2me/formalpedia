-- Prove2me | Theorems.Thm_UnitaryQIPPSPACE_fact_4_10
-- name    : UnitaryQIPPSPACE.fact_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:30:57.64671+00:00
-- url     : https://prove2.me/theorems/105f4c65-a07d-45af-9ce4-054ea8c00443
-- title:
--   Fact 4.10 — phase kickback [CEMM98]
-- statement:
--   For every $f:\{0,1\}^\ell\to\{0,1\}$, let $h(y,t):=t\cdot f(y)$. Then
--   $$O_f=(I\otimes H)\,D_h\,(I\otimes H),$$
--   where $O_f|x,b\rangle=|x,b\oplus f(x)\rangle$ on $\ell+1$ qubits and $H$ acts on the last qubit.
--
--   A query thus reduces to a Boolean phase gate.
--
--   Differences from the source: none.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Fact 4.10 ([CEMM98]), p.26 (PDF p.28)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_boolPhaseGate
import Definitions.Def_UnitaryQIPPSPACE_embed1

namespace UnitaryQIPPSPACE

/-- **Fact 4.10 ([CEMM98])** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*, arXiv:2611.02819, held
version sha256 9e357a00…, p. 26 (PDF p. 28)): "For every Boolean function `f : {0,1}^ℓ → {0,1}`, let
`h(y, t) := t · f(y)` for `y ∈ {0,1}^ℓ`, `t ∈ {0,1}`. Then it holds that `O_f = (I ⊗ H) D_h (I ⊗ H)`."

`O_f` acts on `ℓ + 1` qubits, `y` the first `ℓ` and `t` the last; `I ⊗ H` is `H` on the last qubit. -/
theorem fact_4_10 (ℓ : ℕ) (f : Bits ℓ → Bool) :
    boolOracle f = embed1 gateH (ℓ + 1) ℓ *
      boolPhaseGate (fun u : Bits (ℓ + 1) => u (Fin.last ℓ) && f (Fin.init u)) *
      embed1 gateH (ℓ + 1) ℓ := by sorry

end UnitaryQIPPSPACE
