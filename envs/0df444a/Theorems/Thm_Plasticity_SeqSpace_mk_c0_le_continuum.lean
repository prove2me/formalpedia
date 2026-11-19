-- Prove2me | Theorems.Thm_Plasticity_SeqSpace_mk_c0_le_continuum
-- name    : Plasticity.SeqSpace.mk_c0_le_continuum
-- status  : Proved
-- author  : @scanstone
-- created : 2026-11-18T19:24:43.134211+00:00
-- url     : https://prove2.me/theorems/5d29eb59-d986-4455-aa31-e0a8cdee0ffb
-- title:
--   $c_0(\Gamma)$ has at most continuum many elements when $|\Gamma|\le\mathfrak c$
-- statement:
--   If the set $\Gamma$ has cardinality at most continuum, then $c_0(\Gamma)$ has cardinality at most continuum.
-- source:
--   Standard: every element of c₀(Γ) has countable support, and 𝔠^ℵ₀ = 𝔠

import Definitions.Def_Plasticity_SeqSpace
import Mathlib.SetTheory.Cardinal.Continuum

namespace Plasticity
theorem SeqSpace.mk_c0_le_continuum (Γ : Type*) (hΓ : Cardinal.mk Γ ≤ Cardinal.continuum) :
    Cardinal.mk (c0 Γ) ≤ Cardinal.continuum := by sorry
end Plasticity
