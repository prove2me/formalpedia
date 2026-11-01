-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P47_hardy_fixed_observable_unique
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P47.hardy_fixed_observable_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:31:20.1565+00:00
-- url     : https://prove2.me/theorems/02ba91d1-9e1c-46fc-a905-5352c3de8a07
-- title:
--   Fixed-observable uniqueness of the constructed Hardy state
-- statement:
--   For each party $P\in\{A,B\}$, let $\alpha_P,\beta_P\in\mathbb C$ satisfy $|\alpha_P|^2+|\beta_P|^2=1$ and $0<|\alpha_P|<1$. The unprimed measurement basis is $|0\rangle,|1\rangle$, and the primed basis is $|0'\rangle_P=\alpha_P|0\rangle+\beta_P|1\rangle$, $|1'\rangle_P=\overline{\beta_P}|0\rangle-\overline{\alpha_P}|1\rangle$. Write $|\psi_H\rangle$ for the last vector obtained by the ordered Gram–Schmidt construction (2)–(4), and $p_H(a,b\mid A,B)$ for its Born probabilities.
--
--   Let $S_0$ be the complex span of $|1'1'\rangle$, $|00'\rangle$, and $|0'0\rangle$. All four constructed Gram–Schmidt vectors have norm one, and the three squared normalization denominators are strictly positive. Moreover,
--   $$
--   \dim_{\mathbb C}S_0^\perp=1,\qquad \rho_H=|\psi_H\rangle\langle\psi_H|\text{ is a density matrix satisfying Hardy's four conditions},
--   $$
--   and $|\psi_H\rangle$ cannot be a product of two local vectors. Every positive semidefinite trace-one two-qubit matrix $\rho$ satisfying $p_\rho(00\mid00)>0$, $p_\rho(00\mid10)=p_\rho(00\mid01)=p_\rho(11\mid11)=0$ for these same measurements obeys $\rho=\rho_H$.
--
--   This identifies the state for fixed observables; comparison of density matrices removes the irrelevant global phase.
-- source:
--   Device-independent quantum key distribution based on measurement inputs, arXiv:1308.6447v3, PDF p. 3, II A: unique constructed state for fixed observables

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

namespace QAlgorithms.Papers.Independent.Intakethird100.P47

open scoped ComplexConjugate

open scoped BigOperators

/-- II A, PDF pp.2–3: for fixed observables (3), the constructed Hardy state spans S-perp,
is a normalized entangled state satisfying (1), and is the unique density satisfying (1).
Density equality removes global phase; this does not identify states with different parameters. -/
theorem hardy_fixed_observable_unique (d : HardyParameters) :
    Module.finrank ℂ ((hardySpan d)ᗮ) = 1 ∧
    (∀ i : Fin 4, IsState (hardyGS d i)) ∧
    (∀ i : Fin 3, 0 < gsDenominatorSq
      ((List.ofFn (hardyGS d)).take (i.val + 1)) (hardyPhi d i.succ)) ∧
    IsDensityMatrix (pureDensity (psiH d)) ∧
    HardyConditions (hardyBehavior d (pureDensity (psiH d))) ∧
    (¬ ∃ u v : EuclideanSpace ℂ Bool, psiH d = tensorVec u v) ∧
    (∀ rho : Matrix (Bool × Bool) (Bool × Bool) ℂ,
      IsDensityMatrix rho → HardyConditions (hardyBehavior d rho) →
        rho = pureDensity (psiH d)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P47
