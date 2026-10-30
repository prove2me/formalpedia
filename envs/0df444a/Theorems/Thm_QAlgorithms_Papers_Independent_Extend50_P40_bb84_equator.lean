-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_bb84_equator
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.bb84_equator
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:09:42.676516+00:00
-- url     : https://prove2.me/theorems/27fecf08-2637-4aff-bb4f-c2efe823bf26
-- title:
--   §II.D.2 Eqs.(36)–(38): extension from BB84 states to an equator
-- statement:
--   Let $T$ be a fixed qubit-to-two-qubit CPTP map. Suppose that, separately at each output $j=A,B$, its marginals on all four BB84 equatorial states are radial mixtures with a fixed factor $\eta_j$. Then the same identity holds on every equatorial state $\psi(\varphi)=(|0\rangle+e^{i\varphi}|1\rangle)/\sqrt2$:
--
--   $$
--   \rho_j(\varphi)=\eta_j|\psi(\varphi)\rangle\langle\psi(\varphi)|+(1-\eta_j)I/2.
--   $$
--
--   This uses the radial identities explicitly assumed in footnote 17, not just equality of four numerical fidelities.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 12, §II.D.2 Eqs.(36)–(38): extension from BB84 states to an equator

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P40

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open MeasureTheory Filter

open scoped Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P12 (sigma)

open QAlgorithms.Papers.Independent.Dependency50.P48 (pureFidelity)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P16
  (CloneMap IsBoseInputChannel coherentTensor tensorWithIdentity canonicalCloner
   HasBoseOutput HasBlackCowCoefficient canonicalCoefficient oneMixed)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector siteObservable)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- II.D.2, PDF p.12 Eqs.(36)–(38) and footnote 17: four radial marginal
identities imply the same identity on the entire equator, separately at each output. -/
theorem bb84_equator (T : Superop (Fin 2) (Fin 2 × Fin 2)) (hT : IsChannel T) (etaA etaB : ℝ)
    (h : ∀ theta ∈ ({0, Real.pi / 2, Real.pi, 3 * Real.pi / 2} : Set ℝ),
      traceRight (T (pureDensity (equator theta))) = depol etaA (pureDensity (equator theta)) ∧
      traceLeft (T (pureDensity (equator theta))) = depol etaB (pureDensity (equator theta))) :
    ∀ theta : ℝ,
      traceRight (T (pureDensity (equator theta))) = depol etaA (pureDensity (equator theta)) ∧
      traceLeft (T (pureDensity (equator theta))) = depol etaB (pureDensity (equator theta)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
