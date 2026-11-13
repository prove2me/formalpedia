-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_principal_ideal_spectrum_homeomorphism
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.principal_ideal_spectrum_homeomorphism
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:49:52.625802+00:00
-- url     : https://prove2.me/theorems/ad4242a3-d657-49e9-b662-b6a410178fff
-- title:
--   principal-ideal-spectrum
-- statement:
--   For a nonzero element $a$ of a bounded lattice, the Stone spectrum of the principal ideal $[0,a]$ is canonically homeomorphic to the basic subspace $Q_a(L)$. In the restriction direction,
--
--   $$Q_a(L)\longrightarrow Q([0,a]),\qquad
--   \mathfrak B\longmapsto\mathfrak B\cap[0,a].$$
--
--   The inverse takes upward closure in $L$. No completeness, orthomodularity or compactness assumption is required.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 66, principal-ideal-spectrum

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- principal-ideal-spectrum; de Groote, Observables I, PDF p./pp. 66.
-/
theorem principal_ideal_spectrum_homeomorphism {L : Type u} [Lattice L] [BoundedOrder L] (a : L) (ha : a ≠ ⊥) :
    letI : Bot (Set.Iic a) := ⟨⟨⊥, bot_le⟩⟩
    ∃ h : (stoneBasic a) ≃ₜ StoneSpectrum (Set.Iic a),
      (∀ B, (h B).val = {b | b.val ∈ B.val.val}) ∧
      (∀ C, (h.symm C).val.val = {b | ∃ c ∈ C.val, c.val ≤ b}) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
