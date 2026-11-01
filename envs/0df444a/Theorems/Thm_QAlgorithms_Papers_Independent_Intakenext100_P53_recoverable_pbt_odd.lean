-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P53_recoverable_pbt_odd
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P53.recoverable_pbt_odd
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:25:40.855986+00:00
-- url     : https://prove2.me/theorems/c5fc823e-7420-474a-b3b9-c7c6e7885b48
-- title:
--   Recoverable PBT for an odd number of qubit ports
-- statement:
--   Let $N\ge1$ be odd and set $J=(N+1)/2$. Use the qubit resource $O_{\mathrm{prob}}$ from Eq.(15), the success effects $S_i=\rho^{-1/2}\sigma_i\rho^{-1/2}$, and the failure projector $P_0=I-\operatorname{supp}\rho$. The inverse square root vanishes on the kernel. In the maximal-spin failure sector Alice measures
--   $$e_0=|J,0\rangle,\qquad e_m^\pm=(|J,m\rangle\pm|J,-m\rangle)/\sqrt2,\quad m=1,\ldots,J.$$
--   These vectors form an orthonormal basis of the failure sector, so the success and refined failure effects form a POVM. Each successful port has probability $1/(N+3)$ and teleports the input exactly. Writing $c_N=3/((N+2)(N+3))$, the unnormalized failure state on reference $D$ and all outputs $B$ is
--   $$\omega_0=c_N\sum_{m=-J}^{J}|J,m\rangle\langle J,m|,\qquad\operatorname{tr}\omega_0=\frac3{N+3}.$$
--   Each refined failure outcome has probability $c_N$ and a normalized pure conditional state whose reference marginal is $I_D/2$. There are unitaries $U_z$ on all $N$ output qubits, chosen solely from the classical refinement outcome $z$, such that for every finite reference $R$ and density operator $T$ on $R\otimes C$, recovery followed by retaining a fixed output qubit gives $c_NT$ in branch $z$. Successful port $i$ gives $T/(N+3)$ without correction. With the same Alice measurement, ignoring the refinement and choosing a uniformly random port on failure instead gives
--   $$F=\frac{N}{N+3}.$$
--   At $N=1$ the resource is a singlet and Alice's success singlet plus the three refinement vectors constitute the usual Bell measurement. This is the constructed hybrid of port selection and faithful teleportation using all outputs.
--
--   **Formalization Note** The printed Eq.(16) scalar is corrected as forced by its preceding normalized sandwich; even $N$ is excluded.
-- source:
--   Some remarks on port-based teleportation, arXiv:1506.01555v2, PDF p. 5, IV, Eqs.(16)-(18): recoverable PBT for qubits and odd port count

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P53

open scoped Classical ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

-- Accepted generic matrix and positive-operator interfaces. The support is the
-- orthogonal range projection; all uses below are on positive physical rho.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

/-- PDF pp.3-4, Eqs.(16)-(18), summary p.5: explicit odd-N recoverable PBT.
The printed Eq.(16) coefficient 6*2^N/((N+2)(N+3)) is corrected to
3/((N+2)(N+3)), forced by its preceding sandwich and the normalized Eq.(15).
Unitaries depend only on the classical refinement outcome, precede every input,
and act on all B qubits. The alternative branch is correction-free port selection. -/
theorem recoverable_pbt_odd (N : ℕ) (hN : 1 ≤ N) (hodd : Odd N) :
    let O := probabilisticResource N
    let p0 : ℝ := 3 / (((N : ℝ) + 2) * ((N : ℝ) + 3))
    ExactProbabilistic O (probabilisticSRM 2 N) ∧
    (∀ i : Fin N, pbtBranchProbability O (srm 2 N i) = 1 / ((N : ℝ) + 3)) ∧
    (∀ z : Refinement N, QAlgorithms.IsState (refinementVector N z)) ∧
    (∀ z w : Refinement N, inner ℂ (refinementVector N z) (refinementVector N w) =
      if z = w then 1 else 0) ∧
    (∑ z : Refinement N, refinementEffect N z) = probabilisticSRM 2 N none ∧
    (∀ z : Fin N ⊕ Refinement N, (recoveryMeasurement N z).PosSemidef) ∧
    (∑ z : Fin N ⊕ Refinement N, recoveryMeasurement N z) = 1 ∧
    pbtBranch O (probabilisticSRM 2 N none) =
      (p0 : ℂ) • ∑ k : Fin (N + 2), QAlgorithms.pureDensity (bdDicke N k.val) ∧
    pbtBranchProbability O (probabilisticSRM 2 N none) = 3 / ((N : ℝ) + 3) ∧
    (∀ z : Refinement N, pbtBranchProbability O (refinementEffect N z) = p0 ∧
      ∃ v : EuclideanSpace ℂ (Fin 2 × Ports 2 N), QAlgorithms.IsState v ∧
        pbtBranch O (refinementEffect N z) = (p0 : ℂ) • QAlgorithms.pureDensity v ∧
        QAlgorithms.traceRight (QAlgorithms.pureDensity v) = (1 / 2 : ℂ) • (1 : Op (Fin 2))) ∧
    (∃ U : Refinement N → Op (Ports 2 N),
      (∀ z, U z ∈ Matrix.unitaryGroup (Ports 2 N) ℂ) ∧
      ∀ (R : Type) [Fintype R] [DecidableEq R] (T : Op (R × Fin 2)),
        QAlgorithms.IsDensityMatrix T →
        (∀ i : Fin N, selectPort i (pbtChannelBranch O (srm 2 N i) T) =
          ((1 / ((N : ℝ) + 3) : ℝ) : ℂ) • T) ∧
        (∀ z : Refinement N,
          selectPort (⟨0, by omega⟩ : Fin N)
            (recoverBranch (U z) (pbtChannelBranch O (refinementEffect N z) T)) = (p0 : ℂ) • T)) ∧
    pbtFidelity O (completedSRM 2 N) = (N : ℝ) / ((N : ℝ) + 3) ∧
    probabilisticResource 1 = 1 ∧ srm 2 1 (0 : Fin 1) = portProjector (d := 2) (0 : Fin 1) ∧
    refinementVector 1 (Sum.inl ()) = onePortBell false false ∧
    refinementVector 1 (Sum.inr (0, false)) = onePortBell false true ∧
    refinementVector 1 (Sum.inr (0, true)) = onePortBell true true := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P53

end
