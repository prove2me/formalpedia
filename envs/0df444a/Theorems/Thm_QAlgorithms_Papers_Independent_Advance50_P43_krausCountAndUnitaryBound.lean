-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P43_krausCountAndUnitaryBound
-- name    : QAlgorithms.Papers.Independent.Advance50.P43.krausCountAndUnitaryBound
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:14:37.469598+00:00
-- url     : https://prove2.me/theorems/f2c9dfcb-4bcd-4ee9-8997-6caf5e171516
-- title:
--   Kraus-count refinement and local unitary specialization
-- statement:
--   Let $A,B,C$ be the disjoint nonzero finite spin registers, with dimensions $M_A,M_B,M_C$, let $H=H^\dagger$ be their fixed network Hamiltonian, set $U(t)=e^{-iHt}$, and let $\epsilon_{AB}(t)\ge0$ be an even state-independent operator-norm bound $\|[U(t)^\dagger X_AU(t),Y_B]\|\le\epsilon_{AB}(t)\|X_A\|\|Y_B\|$ for every supported $X_A,Y_B$. Let the density matrix $\tau_{ABC}$ satisfy the finite-network and state-independent LR assumptions described in Eqs. (2)–(6). All register dimensions are positive; $C$ may be one-dimensional. Let $\mathcal E_A(X)=\sum_{k=1}^K F_kXF_k^\dagger$ be an A-local CPTP map with $\sum_kF_k^\dagger F_k=I_A$. Set $\rho_B(t)=\operatorname{Tr}_{AC}[U(t)(\mathcal E_A\otimes\mathrm{id}_{BC})(\tau_{ABC})U(t)^\dagger]$ and $\rho_B^{(0)}(t)=\operatorname{Tr}_{AC}[U(t)\tau_{ABC}U(t)^\dagger]$. With $D(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$,
--
--   $$D(\rho_B(t),\rho_B^{(0)}(t))\le\frac K2\epsilon_{AB}(t).$$
--
--   In particular, for any A-local unitary $V$, the encoding $X\mapsto VXV^\dagger$ has a one-element Kraus presentation and the bound is $\epsilon_{AB}(t)/2$.
--
--   This refinement retains the actual presentation size of the effective A-local encoding; it does not assert that a QA unitary followed by tracing Q induces a unitary on A.
-- source:
--   Quantum-capacity bounds in spin-network communication channels, arXiv:1905.11920v2, PDF p. 5, §III.A, Eq.(41)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P43

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45
  (holevoCapacity resourceCapacity standardEbit)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer diamond)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst privateCapacity)

open QAlgorithms.Papers.Independent.Information100.P22 (quantumCapacity)

open QAlgorithms.Papers.Independent.Dependency50.P23 (ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

variable {A B C Q : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype Q]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq Q]

/-- arXiv:1905.11920v2, PDF p.5, (41): K counts Kraus operators of the effective
A-local map. The unitary clause concerns an A-local unitary, not an arbitrary
unitary on QA followed by discarding Q. -/
theorem krausCountAndUnitaryBound [Nonempty A] [Nonempty B] [Nonempty C]
    (D : LRData A B C)
    (tau : Matrix (A × (B × C)) (A × (B × C)) ℂ) (htau : IsDensityMatrix tau)
    (t : ℝ) :
    (∀ (K : ℕ) (F : Fin K → Matrix A A ℂ), IsKrausFamily F →
      traceNorm (receive D t (mapFirst (krausApply F) tau) - receive D t tau) / 2 ≤
        ((K : ℝ) / 2) * D.epsilon t) ∧
    (∀ V : Matrix.unitaryGroup A ℂ,
      traceNorm (receive D t (mapFirst (conjSuperop (V : Matrix A A ℂ)) tau) -
        receive D t tau) / 2 ≤ D.epsilon t / 2) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P43

end
