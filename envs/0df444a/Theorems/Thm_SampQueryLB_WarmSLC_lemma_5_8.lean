-- Prove2me | Theorems.Thm_SampQueryLB_WarmSLC_lemma_5_8
-- name    : SampQueryLB.WarmSLC.lemma_5_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:17:09.506235+00:00
-- url     : https://prove2.me/theorems/7943b136-a59c-4cb3-9d61-0b53f35fb799
-- title:
--   Lemma 5.8 — locality of the measurements of earlier fields: $\|P_{O_A}P_{O_B}\|_{op}\le2\sqrt{st}\exp(-Kr^2/(4st))$
-- statement:
--   Consider the hard family of §4.1 and a level $i$. Let $s,t\ge1$ be integers with $K\ge2st$ and let $r>0$. Let $A,B\subset\mathbb R^{(h+1)n}$ be finite with $|A|\le s$, $|B|\le t$, such that $\|\psi_i(x)-\psi_i(y)\|\ge r$ and $\|\psi_i(x)+\psi_i(y)\|\ge r$ whenever $x\in A$, $y\in B$, $C_i(x)C_i(y)>0$. Put
--   $$O_A=\mathrm{span}\{\Phi_{j,p}(x),D_v\Phi_{j,p}(x):j<i,\ p\in\mathcal P,\ x\in A,\ v\in\mathbb R^{(h+1)n}\}\subseteq G_{<i}$$
--   and $O_B$ likewise.
--
--   **Lemma 5.8.** $\|P_{O_A}P_{O_B}\|_{op}\le2\sqrt{st}\exp\big(-\frac{Kr^2}{4st}\big)$.
--
--   Queries at directions separated at level $i$ therefore measure nearly orthogonal parts of all the earlier fields, which is the hypothesis of the decoupling theorem.
--
--   **Formalization Note.** $O_A$ is `obsSpan i A`, a subspace of the whole coefficient space $G_n$ (its vectors are supported on the levels $j<i$); $D_v\Phi_{j,p}(x)$ is `fderiv ℝ (feat j p) x v`; $P_W$ is `W.starProjection`.
--
--   Differences from the source:
--   - reading: the standing assumption of §4.1 that n is a sufficiently large integer → ∃ n0, ∀ n ≥ n0; reason: the construction is set up for large n only (§4.1); the statement itself has no constants C_f, C_g, η*, λ*
--   - encoding: x = (x_0, …, x_h) ∈ R^{d_n} with blocks x_j ∈ R^n; tensors in R^{n^{pS_i}} with ψ_i = u_i ⊗ u_{i+1}^{⊗K} ⊗ ⋯ → Point (dn n) with block j at coordinates finProdFinEquiv (j, a); G_n = EuclideanSpace on Σ (i,p), (Fin (p·S_i) → Fin n), slot r of ψ_i carrying block i + slotLevel K r; reason: a fixed labelling of coordinates and tensor slots; every statement is invariant under it
--   - encoding: §5.3 fixes 1 ≤ i ≤ h → every level 0 ≤ i ≤ h; reason: at i = 0 there is no level j < i, so every measurement vector is zero and the statement holds trivially; no instance of the source changes
-- source:
--   Zhou, Suzuki, Towards the Query Complexity of Sampling under Strong Log-Concavity and Log-Sobolev Inequalities, arXiv:2611.05813 (held version dated November 3, 2026, sha256 966f8fc0…184c), p. 43, Lemma 5.8 (PDF p. 46)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_SampQueryLB_WarmSLC_Model
import Definitions.Def_SampQueryLB_WarmSLC_HardFamily
import Definitions.Def_SampQueryLB_WarmSLC_Experiments

open MeasureTheory OAI.LogConcaveSampling ProbabilityTheory Filter
open scoped ENNReal ContDiff RealInnerProductSpace Topology

namespace SampQueryLB.WarmSLC

theorem lemma_5_8 :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ (i : Lvl n) (s t : ℕ), 1 ≤ s → 1 ≤ t → 2 * s * t ≤ KK n →
      ∀ r : ℝ, 0 < r → ∀ A B : Finset (Point (dn n)), A.card ≤ s → B.card ≤ t →
        (∀ x ∈ A, ∀ y ∈ B, 0 < Ccut i x * Ccut i y →
          r ≤ ‖psi i x - psi i y‖ ∧ r ≤ ‖psi i x + psi i y‖) →
        ‖(obsSpan i (A : Set (Point (dn n)))).starProjection ∘L
            (obsSpan i (B : Set (Point (dn n)))).starProjection‖ ≤
          2 * Real.sqrt ((s : ℝ) * t) * Real.exp (-((KK n : ℝ) * r ^ 2 / (4 * s * t))) := by sorry

end SampQueryLB.WarmSLC
