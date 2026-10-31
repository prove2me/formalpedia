-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_max_divergence_pinching
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.max_divergence_pinching
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:44:03.596152+00:00
-- url     : https://prove2.me/theorems/f9f1ccb5-6196-458f-a1e0-4b32a6f13247
-- title:
--   §4.2.4 (4.40)–(4.43): max-divergence pinching attainment
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion.
--
--   D∞(Pσρ||σ)≤D∞(ρ||σ)≤D∞(Pσρ||σ)+log|specσ|. After tensor powers and division by n the correction vanishes because |spec(σ^⊗n)|≤(n+1)^(d−1); obtain the limit representation.
--
--   $$
--   D_{\max}(\mathcal P_\sigma\rho\|\sigma)\le D_{\max}(\rho\|\sigma)\le D_{\max}(\mathcal P_\sigma\rho\|\sigma)+\log_2|\operatorname{spec}\sigma|,\quad|\operatorname{spec}(\sigma^{\otimes n})|\le(n+1)^{d-1}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 60, §4.2.4 (4.40)–(4.43): max-divergence pinching attainment

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P07

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z]

/-- NODE paper:1504.00233#4.maxpinching
§4.2.4 (4.40)–(4.43): max-divergence pinching attainment, arXiv:1504.00233v5, PDF p.60,61. -/
theorem max_divergence_pinching [Nonempty I] (r s : paperMat I) (hr : r.PosSemidef)
    (hne : r ≠ 0) (hs : s.PosSemidef) :
    maxD (paperPinch s r) s ≤ maxD r s ∧ maxD r s ≤ maxD (paperPinch s r) s+(Real.logb 2 (spectralValues s).card:EReal) ∧
    (∀ n : ℕ, 0 < n → (spectralValues (paperTensorPower s n)).card ≤ (n+1)^(Fintype.card I-1)) ∧
    Tendsto (fun n : ℕ => Real.logb 2 (spectralValues (paperTensorPower s n)).card/(n:ℝ)) atTop (nhds 0) ∧
    Tendsto (fun n : ℕ => ((1/(n:ℝ):ℝ):EReal)*maxD (paperTensorPower r n) (paperTensorPower s n)) atTop (nhds (maxD r s)) ∧
    Tendsto (fun n : ℕ => ((1/(n:ℝ):ℝ):EReal)*maxD (paperPinch (paperTensorPower s n) (paperTensorPower r n)) (paperTensorPower s n))
      atTop (nhds (maxD r s)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
