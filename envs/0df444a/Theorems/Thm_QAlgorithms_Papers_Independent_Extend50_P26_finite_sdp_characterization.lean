-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P26_finite_sdp_characterization
-- name    : QAlgorithms.Papers.Independent.Extend50.P26.finite_sdp_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:30:17.153985+00:00
-- url     : https://prove2.me/theorems/f74e159d-0d55-4b39-a0f2-210671bda2a4
-- title:
--   Finite exact-inversion SDP characterization and attained maximum
-- statement:
--   Let $d\ge2$ and $k\ge1$ be integers and choose the parallel, adaptive, or general process-matrix class. Write $J(U)$ for the unnormalized Choi operator of a forward unitary channel. There is a finite family $U_1,\ldots,U_m\in SU(d)$ whose tensors $J(U_i)^{\otimes k}$ are linearly independent and span all repeated-unitary tensors. There is also a finite real affine presentation of deterministic admissibility in the chosen class. The attainable universal exact-inversion probabilities are precisely the feasible values of $p\in[0,1]$ in
--
--   $$\max p\quad\text{subject to}\quad S*J(U_i)^{\otimes k}=pJ(U_i^\dagger)\ (1\le i\le m),\quad S\succeq0,\quad C-S\succeq0,\quad C\text{ deterministic in the chosen class}.$$
--
--   The maximum is attained. Here $*$ is the link product, $S$ is the success branch, and $C$ is its deterministic completion. Both are fixed independently of the unknown input unitary. Choi equality imposes exactness also with arbitrary reference systems.
--
--   This supplies finite semidefinite constraints without weakening universal inversion to sampled inputs. The positive-use restriction is necessary for the basis reduction; no finite Haar-sampling confidence bound is asserted.
-- source:
--   Reversing Unknown Quantum Transformations: Universal Quantum Circuit for Inverting General Unitary Operations, arXiv:1810.06944v3, PDF p. 4, Eq.(4)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P26

noncomputable section

open QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P26

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF p.4, Eq.(4): a basis of the actual repeated-unitary Choi tensors gives exactly
the universal feasible probabilities, with an attained maximum. All deterministic
constraints admit a finite real affine presentation, so this is a finite SDP.
The positive-use restriction k>=1 corrects the printed basis reduction at k=0:
a single scalar input basis cannot constrain an unknown inverse output channel.
No arbitrary linear target relation is assumed: inverseChoi is constructed from U. -/
theorem finite_sdp_characterization (d k : ℕ) (hd : 2 ≤ d) (hk : 1 ≤ k)
    (c : CircuitClass) :
    ∃ (m : ℕ) (U : Fin m → (Matrix.specialUnitaryGroup (Fin d) ℂ)),
      LinearIndependent ℂ (fun j => slotTensor d k (fun _ => unitaryChoi (U j).val)) ∧
      Submodule.span ℂ (Set.range (fun j => slotTensor d k (fun _ => unitaryChoi (U j).val))) =
        Submodule.span ℂ (Set.range (fun V : (Matrix.specialUnitaryGroup (Fin d) ℂ) =>
          slotTensor d k (fun _ => unitaryChoi V.val))) ∧
      (∃ (t : ℕ) (L : Fin t → ((Matrix (InversionBasis d (k+1)) (InversionBasis d (k+1)) ℂ) →ₗ[ℝ] ℝ)) (b : Fin t → ℝ),
        ∀ C, InversionCompletion c d k C ↔ C.PosSemidef ∧ ∀ j, L j C = b j) ∧
      (∀ p : ℝ, FiniteFeasible c d k m U p ↔ Attainable c d k p) ∧
      ∃ p : ℝ, FiniteFeasible c d k m U p ∧
        ∀ q : ℝ, FiniteFeasible c d k m U q → q ≤ p := by sorry

end QAlgorithms.Papers.Independent.Extend50.P26

end
