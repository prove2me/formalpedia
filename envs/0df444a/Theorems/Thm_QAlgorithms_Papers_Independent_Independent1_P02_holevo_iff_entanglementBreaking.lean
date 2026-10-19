-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_holevo_iff_entanglementBreaking
-- name    : QAlgorithms.Papers.Independent.Independent1.P02.holevo_iff_entanglementBreaking
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:18:43.276294+00:00
-- url     : https://prove2.me/theorems/4495818d-8a2f-423f-b87c-fdad990760f0
-- title:
--   Theorem 2: Holevo form iff entanglement breaking; trace-preserving normalization
-- statement:
--   Let $d\ge1$ and let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be complex-linear. A finite Holevo representation with density matrices $R_k$ and positive semidefinite effects $F_k$ exists if and only if $\Phi$ breaks entanglement in the separable-positive-cone sense.
--
--   $$\Phi(X)=\sum_k\operatorname{Tr}(F_kX)R_k\quad\Longleftrightarrow\quad\Phi\text{ is entanglement breaking}.$$
--
--   For every supplied such representation, trace preservation is equivalent to $\{F_k\}$ being a POVM. For every supplied representation (2) with unit output vectors $\psi_k$, it is equivalent to $\sum_k|\phi_k\rangle\langle\phi_k|=I$; the input vectors $\phi_k$ need not be unit or nonzero.
--
--   This identifies measure-and-prepare maps without presupposing complete positivity or trace preservation.
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, Theorem 2: Holevo form iff entanglement breaking; trace-preserving normalization, PDF p. 2. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

/-!
# Entanglement Breaking Channels (quant-ph/0302031v2)

All reference factors occur first. General EB uses the separable positive cone;
EBT additionally preserves trace. Proposed source corrections below require
independent source moderation; see MODERATION_NOTES.md in the assigned unit.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P02


















































/-- Theorem 2, PDF p.2, proof pp.5–6: general equivalence and normalization
for each supplied Holevo or rank-one representation. -/
theorem holevo_iff_entanglementBreaking (d : ℕ) (hd : 0 < d) (Phi : Endomorphism d) :
    (HasHolevoRepresentation Phi false ↔ Entanglement.IsEntanglementBreakingPositive Phi) ∧
    (∀ (m : ℕ) (R F : Fin m → Algebra d), (∀ k, IsDensityMatrix (R k)) →
      (∀ k, (F k).PosSemidef) → Phi = Entanglement.holevoMap R F →
      (PreservesTrace Phi ↔ IsPOVM F)) ∧
    (∀ (m : ℕ) (psi phi : Fin m → StateVector d), (∀ k, IsState (psi k)) →
      Phi = Entanglement.holevoMap (fun k => pureDensity (psi k)) (fun k => pureDensity (phi k)) →
      (PreservesTrace Phi ↔ ∑ k, pureDensity (phi k) = 1)) := by sorry



















end QAlgorithms.Papers.Independent.Independent1.P02
