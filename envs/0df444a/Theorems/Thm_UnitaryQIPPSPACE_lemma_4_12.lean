-- Prove2me | Theorems.Thm_UnitaryQIPPSPACE_lemma_4_12
-- name    : UnitaryQIPPSPACE.lemma_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:31:35.504197+00:00
-- url     : https://prove2.me/theorems/6f1babfd-9c42-4915-af43-a90075e32642
-- title:
--   Lemma 4.12 — Boolean queries from phase states
-- statement:
--   For every sequence of measurement outcomes $a=(a_1,\dots,a_m)$, the phase-state injection procedure acts on $\mathcal H_Q$ by
--   $$M_a=\frac{\chi_a}{\sqrt{2^{m^2}}}D_g$$
--   for some $\chi_a\in\{+1,-1\}$. Consequently, discarding the outcomes yields $\sum_aM_a(\cdot)M_a^\dagger=D_g(\cdot)D_g^\dagger$.
--
--   Phase states thus implement a Boolean phase gate exactly.
--
--   Differences from the source: none.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Lemma 4.12, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_injKraus

open Matrix

namespace UnitaryQIPPSPACE

/-- **Lemma 4.12 (Boolean queries from phase state, cf. [DGH+25, Sections 2.3, 4.5, 4.6])** (He, Ou,
Zhao, *unitaryQIP = unitaryPSPACE*, arXiv:2611.02819, held version sha256 9e357a00…, p. 28 (PDF
p. 30)): "For every sequence of measurement outcomes `a = (a₁, a₂, …, a_m)`, the above phase-state
injection procedure acts only nontrivially on `H_Q` by the operator `M_a := χ_a/√(2^{m²}) · D_g` for
some `χ_a ∈ {+1, −1}`. Consequently, discarding the outcomes yields `𝒟_g(·) = D_g(·)D_g†` as
desired."

`M_a` is the operator by which the procedure acts on `Q` on the outcomes `a` (`injKraus`, built from
the procedure's rounds); discarding the outcomes is the sum over all `a` of `M_a(·)M_a†`. -/
theorem lemma_4_12 (m : ℕ) (g : Bits m → Bool) :
    (∀ a : Fin m → Bits m, ∃ χ : ℂ, (χ = 1 ∨ χ = -1) ∧
      injKraus g (List.ofFn a) = (χ / (Real.sqrt (2 ^ (m ^ 2)) : ℂ)) • boolPhaseGate g) ∧
    ∀ ρ : Matrix (Bits m) (Bits m) ℂ,
      ∑ a : Fin m → Bits m, injKraus g (List.ofFn a) * ρ * (injKraus g (List.ofFn a))ᴴ =
        boolPhaseGate g * ρ * (boolPhaseGate g)ᴴ := by sorry

end UnitaryQIPPSPACE
