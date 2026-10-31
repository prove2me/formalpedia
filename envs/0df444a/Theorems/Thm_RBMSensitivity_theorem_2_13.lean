-- Prove2me | Theorems.Thm_RBMSensitivity_theorem_2_13
-- name    : RBMSensitivity.theorem_2_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:35:13.408982+00:00
-- url     : https://prove2.me/theorems/63f73180-b786-470e-b0ff-30e574ccd133
-- title:
--   Theorem 2.13 — pathwise unique derivative process
-- statement:
--   Suppose the data $\{(d_i(\cdot),n_i),i\in\mathcal I\}$ satisfies Assumptions 2.2, 2.4 and 2.5 and $b(\cdot)$, $\sigma(\cdot)$ and $R(\cdot)$ satisfy Assumption 2.12. Then given $\alpha\in U$, $x\in G$, $y\in\mathbb H_x$ and a $J$-dimensional $\{\mathcal F_t\}$-adapted Brownian motion $W$, there exists a pathwise unique derivative process along the RBM $Z^{\alpha,x}$ starting at $y$, denoted $\mathcal J^{\alpha,\xi}$, where $\xi:=(x,y)$. In other words, if $\mathcal J^{\alpha,\xi}$ and $\tilde{\mathcal J}^{\alpha,\xi}$ are both derivative processes along $Z^{\alpha,x}$ that satisfy $\mathcal J^{\alpha,\xi}(0)=\tilde{\mathcal J}^{\alpha,\xi}(0)=y$, then almost surely $\mathcal J^{\alpha,\xi}(t)=\tilde{\mathcal J}^{\alpha,\xi}(t)$ for all $t\ge 0$.
--
--   This defines the joint process $(Z^{\alpha,x},\mathcal J^{\alpha,\xi})$ on $\mathbb X$. It is quoted in the paper from Lipshutz and Ramanan's earlier work.
--
--   Differences from the source:
--   - encoding: J-dimensional {F_t}-Brownian motion, defined by quadratic variation → IsFBrownian: adapted, a.s. continuous, started at 0, increments independent of F_s with law N(0,(t-s)E_J); reason: Lévy's characterization; quadratic variation is absent from Mathlib at this revision; same object
--   - encoding: the RBM Z^{α,x} → any RBM Z driven by W with Z(0) = x a.s.; reason: pathwise uniqueness (Theorem 2.8) makes the choice immaterial
--   - encoding: continuous Z, Y (Definition 2.1) and RCLL J, K (Definition 2.10) processes → paths continuous, resp. RCLL, for almost every ω; reason: under the usual conditions a process with a.s. continuous (RCLL) paths is indistinguishable from an adapted process all of whose paths are continuous (RCLL): modify it on a P-null set, which lies in F_0; same processes up to indistinguishability
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Theorem 2.13, p.8 (cited: [25, Corollary 3.15])

import Mathlib
import Definitions.Def_RBMSensitivity_IsUsualFiltration
import Definitions.Def_RBMSensitivity_Data_Assumption_2_2
import Definitions.Def_RBMSensitivity_Data_Assumption_2_4
import Definitions.Def_RBMSensitivity_Data_Assumption_2_5
import Definitions.Def_RBMSensitivity_Data_Assumption_2_12
import Definitions.Def_RBMSensitivity_Data_IsRBM
import Definitions.Def_RBMSensitivity_Data_IsDerivativeProcess
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- **Theorem 2.13** ([25, Corollary 3.15]): arXiv:1907.00472v2, p.8. Under Assumptions 2.2, 2.4, 2.5 and
2.12, given `α ∈ U`, `x ∈ G`, `y ∈ H_x` and `W`, there is a pathwise unique derivative process along the
RBM `Z^{α,x}` starting at `y`. -/
theorem theorem_2_13 {J : ℕ} (hJ : 0 < J) (D : Data J) {B : ℝ → Set (E J)}
    (h22 : D.Assumption_2_2) (h24 : D.Assumption_2_4 B) (h25 : D.Assumption_2_5)
    (h212 : D.Assumption_2_12)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (h𝓕 : IsUsualFiltration 𝓕 P)
    {W : ℝ≥0 → Ω → E J} (hW : IsFBrownian 𝓕 P W)
    {α : ℝ} (hα : α ∈ D.U) {x y : E J} (hx : x ∈ D.G) (hy : y ∈ D.H x)
    {Z : ℝ≥0 → Ω → E J} (hZ : D.IsRBM 𝓕 P W α Z) (hZ0 : ∀ᵐ ω ∂P, Z 0 ω = x) :
    (∃ 𝒥 : ℝ≥0 → Ω → E J, D.IsDerivativeProcess 𝓕 P W α Z 𝒥 ∧ ∀ᵐ ω ∂P, 𝒥 0 ω = y) ∧
    ∀ 𝒥 𝒥' : ℝ≥0 → Ω → E J, D.IsDerivativeProcess 𝓕 P W α Z 𝒥 →
      D.IsDerivativeProcess 𝓕 P W α Z 𝒥' → (∀ᵐ ω ∂P, 𝒥 0 ω = y) → (∀ᵐ ω ∂P, 𝒥' 0 ω = y) →
      ∀ᵐ ω ∂P, ∀ t, 𝒥 t ω = 𝒥' t ω := by sorry

end RBMSensitivity
