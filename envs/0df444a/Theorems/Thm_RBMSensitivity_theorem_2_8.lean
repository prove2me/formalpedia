-- Prove2me | Theorems.Thm_RBMSensitivity_theorem_2_8
-- name    : RBMSensitivity.theorem_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:33:59.292651+00:00
-- url     : https://prove2.me/theorems/eb533cb4-ab6f-4a2f-aefd-b6f7cd34bb50
-- title:
--   Theorem 2.8 — pathwise unique, strong Markov RBM
-- statement:
--   Suppose the data $\{(d_i(\cdot),n_i),i\in\mathcal I\}$ satisfies Assumptions 2.4 and 2.5. Then given $\alpha\in U$, $x\in G$, and a $J$-dimensional $\{\mathcal F_t\}$-adapted Brownian motion $W$ on $(\Omega,\mathcal F,\mathbb P)$, there exists a pathwise unique RBM associated with $\alpha$ starting at $x$, denoted $Z^{\alpha,x}$. In other words, if $Z^{\alpha,x}$ and $\tilde Z^{\alpha,x}$ are both RBMs associated with $\alpha$ and driving Brownian motion $W$ that almost surely satisfy $Z^{\alpha,x}(0)=\tilde Z^{\alpha,x}(0)=x$, then almost surely $Z^{\alpha,x}(t)=\tilde Z^{\alpha,x}(t)$ for all $t\ge 0$. Moreover, $Z^{\alpha,x}$ is a strong Markov process.
--
--   This result supplies the objects of the whole mission, and it shows that the choice of family of RBMs in the later statements is immaterial. The paper quotes it from Ramanan (2006).
--
--   Differences from the source:
--   - encoding: J-dimensional {F_t}-Brownian motion, defined by quadratic variation → IsFBrownian: adapted, a.s. continuous, started at 0, increments independent of F_s with law N(0,(t-s)E_J); reason: Lévy's characterization; quadratic variation is absent from Mathlib at this revision; same object
--   - reading: "strong Markov process", not spelled out in the paper → IsStrongMarkovAt: E[g(Z(τ+t)) | F_τ] = (T_t g)(Z(τ)) a.s. on {τ < ∞}, with T_t g(y) := E g(Z^{α,y}(t)); reason: the standard meaning of the term
--   - encoding: continuous Z, Y (Definition 2.1) and RCLL J, K (Definition 2.10) processes → paths continuous, resp. RCLL, for almost every ω; reason: under the usual conditions a process with a.s. continuous (RCLL) paths is indistinguishable from an adapted process all of whose paths are continuous (RCLL): modify it on a P-null set, which lies in F_0; same processes up to indistinguishability
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Theorem 2.8, p.7 (cited: [30, Theorem 4.3])

import Mathlib
import Definitions.Def_RBMSensitivity_IsUsualFiltration
import Definitions.Def_RBMSensitivity_Data_Assumption_2_4
import Definitions.Def_RBMSensitivity_Data_Assumption_2_5
import Definitions.Def_RBMSensitivity_Data_IsRBM
import Definitions.Def_RBMSensitivity_IsStrongMarkovAt
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- **Theorem 2.8** ([30, Theorem 4.3]): arXiv:1907.00472v2, p.7. Under Assumptions 2.4 and 2.5, given
`α ∈ U`, `x ∈ G` and a Brownian motion `W`, there is a pathwise unique RBM associated with `α` starting
at `x`, and it is a strong Markov process.

**Formalization Note.** Assumption 2.2 is not a hypothesis, as in the paper. The strong Markov clause
is for a family of RBMs from all starting points of `G`, which the first clause provides. -/
theorem theorem_2_8 {J : ℕ} (hJ : 0 < J) (D : Data J) {B : ℝ → Set (E J)}
    (h24 : D.Assumption_2_4 B) (h25 : D.Assumption_2_5)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (h𝓕 : IsUsualFiltration 𝓕 P)
    {W : ℝ≥0 → Ω → E J} (hW : IsFBrownian 𝓕 P W)
    {α : ℝ} (hα : α ∈ D.U) {x : E J} (hx : x ∈ D.G) :
    (∃ Z : ℝ≥0 → Ω → E J, D.IsRBM 𝓕 P W α Z ∧ ∀ᵐ ω ∂P, Z 0 ω = x) ∧
    (∀ Z Z' : ℝ≥0 → Ω → E J, D.IsRBM 𝓕 P W α Z → D.IsRBM 𝓕 P W α Z' →
      (∀ᵐ ω ∂P, Z 0 ω = x) → (∀ᵐ ω ∂P, Z' 0 ω = x) → ∀ᵐ ω ∂P, ∀ t, Z t ω = Z' t ω) ∧
    ∀ Zf : E J → ℝ≥0 → Ω → E J,
      (∀ y ∈ D.G, D.IsRBM 𝓕 P W α (Zf y) ∧ ∀ᵐ ω ∂P, Zf y 0 ω = y) →
      IsStrongMarkovAt 𝓕 P Zf x := by sorry

end RBMSensitivity
