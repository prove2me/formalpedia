-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P24_kacEffectiveSemigroup
-- name    : QAlgorithms.Papers.Independent.Renew46.P24.kacEffectiveSemigroup
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:51:44.331335+00:00
-- url     : https://prove2.me/theorems/f079bfe1-253f-44bc-8f57-a5e411948bdf
-- title:
--   §4.3: effective channel and its semigroup law
-- statement:
--   Let $\mu\in[-1,1]$, let $V$ be a fixed $2\times2$ unitary, and let $\nu=(I+\mathbf m\cdot\boldsymbol\sigma)/2$ be a normalized positive qubit density matrix. Define the effective channel
--
--   $$\Lambda_\mu(\nu)=\frac{1-\mu}{2}V\nu V^*+\frac{1+\mu}{2}\nu.$$
--
--   For every natural time $t$, the reduced density is $\nu_t=\Lambda_\mu^t(\nu)$, remains a normalized positive density matrix, and equals $(I+\mathbf m_t\cdot\boldsymbol\sigma)/2$, where $\mathbf m_t$ iterates the Bloch-vector step of this channel. For all natural $s,t$,
--
--   $$\Lambda_\mu^{t+s}(\nu)=\Lambda_\mu^t(\Lambda_\mu^s(\nu)).$$
--
--   The iterate identity holds for every input matrix. This states the explicit discrete effective evolution and semigroup law; the externally cited proof of the microscopic autonomous limit is outside this target.
-- source:
--   Quantum Macrostates, Equivalence of Ensembles and an H-Theorem, arXiv:math-ph/0601027v2, PDF p. 15, §4.3: effective channel and its semigroup law

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P24

open Filter

open scoped Topology ComplexOrder Matrix.Norms.L2Operator

-- Exact primitives verified against the pinned accepted-library SHA256 catalogue.

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Dependency50.P21 (spectralFunction relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.15, (4.11): the explicit effective Kac evolution is the discrete
iterate of the printed channel, represents the evolved Bloch density, and is a semigroup.
No microscopic autonomous-limit theorem from the externally cited [4] is asserted here. -/
theorem kacEffectiveSemigroup (mu : ℝ) (hmu : mu ∈ Set.Icc (-1) 1)
    (V : Matrix.unitaryGroup Bool ℂ) (m : Fin 3 → ℝ)
    (hnu : QAlgorithms.IsDensityMatrix (blochDensity m)) :
    (∀ t : ℕ, (kacChannel mu V)^[t] (blochDensity m) =
      blochDensity ((kacSpinStep mu V)^[t] m) ∧
      QAlgorithms.IsDensityMatrix ((kacChannel mu V)^[t] (blochDensity m))) ∧
    ∀ (s t : ℕ) (nu : Matrix Bool Bool ℂ),
      (kacChannel mu V)^[t + s] nu =
        (kacChannel mu V)^[t] ((kacChannel mu V)^[s] nu) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P24

end
