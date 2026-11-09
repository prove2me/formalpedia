-- Prove2me | Theorems.Thm_ScalablePassiveQRAM_Device_deterministic_transfer
-- name    : ScalablePassiveQRAM.Device.deterministic_transfer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:56:27.43621+00:00
-- url     : https://prove2.me/theorems/f5a0a60b-5445-4a39-abcb-2b119467f82d
-- title:
--   Lemma 5 — Deterministic transfer on the history path
-- statement:
--   For a path with $L+1$ sites, $L\ge0$, and $\Omega>0$, use couplings $J_j=(\Omega/2)\sqrt{j(L-j+1)}$. At transfer time $\tau=\pi/\Omega$,
--
--   $$e^{-iH_{\rm path}\pi/\Omega}|0\rangle=e^{-i\pi L/2}|L\rangle.$$
--
--   The phase is the exact phase computed in equation (33), so it depends only on path length. This supplies perfect transfer with unit amplitude, including the empty path.
--
--   Differences from the source:
--   - encoding: a phase depending only on L → the exact phase −πL/2 from equation (33); reason: the proof computes this phase explicitly
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), Lemma 5, p. 19. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Energy
import Mathlib

open scoped BigOperators Matrix
set_option synthInstance.maxSize 10000
noncomputable section

namespace ScalablePassiveQRAM.Device
local instance deterministic_transferDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance deterministic_transferDecidableEq (a : Type) : DecidableEq a := Classical.decEq a

theorem deterministic_transfer (L : ℕ) (Ω : ℝ) (hΩ : 0 < Ω) :
    evolve (pathHamiltonian L Ω) (Real.pi / Ω) *ᵥ ket (⟨0,by omega⟩ : Fin (L+1)) =
      Complex.exp (Complex.I * (phase L : ℂ)) • ket (⟨L,by omega⟩ : Fin (L+1)) := by sorry

end ScalablePassiveQRAM.Device
