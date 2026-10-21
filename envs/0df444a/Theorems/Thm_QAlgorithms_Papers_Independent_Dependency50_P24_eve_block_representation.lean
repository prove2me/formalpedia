-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_eve_block_representation
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.eve_block_representation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:28:15.184756+00:00
-- url     : https://prove2.me/theorems/1b3ae072-4aff-40cd-862f-ced3acb738a0
-- title:
--   §VI-B and XV-A: Eve-conditioned blocks and fidelity
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   Let $|\psi\rangle$ be a unit purification, $a=(i,j)$ a key index, and $p_a$ its outcome probability. Let $C_a(s,e)$ be the normalized conditional amplitude matrix; at $p_a=0$ choose a normalized basis vector. Set $\rho_E^a=(C_a^\dagger C_a)^T$, and let $A_{ab}$ be the shield block of the actual Eve-traced state. Then $p_a\ge0$, $\sum_ap_a=1$, every $\rho_E^a$ is a state, and
--
--   $$A_{ab}=\sqrt{p_ap_b}\,C_aC_b^\dagger,\qquad\|A_{ab}\|_1=\sqrt{p_ap_b}\,F(\rho_E^a,\rho_E^b).$$
--
--   There are rectangular support partial isometries $V_a$ such that $C_a=V_a\sqrt{(\rho_E^a)^T}$, $V_a^\dagger V_a$ is the support projector of $(\rho_E^a)^T$, and $V_aV_a^\dagger$ is the support projector of $C_aC_a^\dagger$. In particular
--
--   $$A_{ab}=\sqrt{p_ap_b}\,V_a\sqrt{(\rho_E^a)^T}\sqrt{(\rho_E^b)^T}V_b^\dagger.$$
--
--   This is the block representation through Eve's conditional states, with transpose placement fixed by the stated coefficient convention.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 15, §VI-B and XV-A: Eve-conditioned blocks and fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

/-- PDF pp.15–16, Eqs.(97)–(98); pp.31–32: actual coefficient blocks and Eve fidelity.
The printed maps from the whole shield onto Eve support in (97),(199) cannot be
isometries when the conditional rank is smaller than the shield dimension. Use polar
partial isometries with the explicitly specified initial and final support projections.
Transposes follow C(s,e)=<s,e|psi_a>; no full-rank assumption is added. -/
theorem eve_block_representation {d : ℕ} [NeZero d] {S T E : Type*}
    [Fintype S] [Fintype T] [Fintype E] [Nonempty S] [Nonempty T] [Nonempty E]
    (psi : EuclideanSpace ℂ ((Key d × (S × T)) × E)) (hpsi : IsState psi) :
    (∀ a, 0 ≤ outcomeWeight psi a ∧ IsDensityMatrix (conditionalEve psi a)) ∧
    (∑ a, outcomeWeight psi a) = 1 ∧
    (∀ a b, keyBlock (traceRight (pureDensity psi)) a b =
      ((Real.sqrt (outcomeWeight psi a * outcomeWeight psi b) : ℝ) : ℂ) •
        (conditionalAmplitude psi a * (conditionalAmplitude psi b)ᴴ)) ∧
    (∀ a b, traceNorm (keyBlock (traceRight (pureDensity psi)) a b) =
      Real.sqrt (outcomeWeight psi a * outcomeWeight psi b) *
        rootFidelity (conditionalEve psi a) (conditionalEve psi b)) ∧
    ∃ V : Key d → Matrix (S × T) E ℂ,
      (∀ a, (V a)ᴴ * V a = supportProjector (conditionalEve psi a).transpose ∧
        V a * (V a)ᴴ = supportProjector
          (conditionalAmplitude psi a * (conditionalAmplitude psi a)ᴴ) ∧
        conditionalAmplitude psi a = V a * cfc Real.sqrt (conditionalEve psi a).transpose) ∧
      ∀ a b, keyBlock (traceRight (pureDensity psi)) a b =
        ((Real.sqrt (outcomeWeight psi a * outcomeWeight psi b) : ℝ) : ℂ) •
          (V a * cfc Real.sqrt (conditionalEve psi a).transpose *
            cfc Real.sqrt (conditionalEve psi b).transpose * (V b)ᴴ) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
