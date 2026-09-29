-- Prove2me | Theorems.Thm_QFS_lemma_lebesgue_diff_paper
-- name    : QFS.lemma_lebesgue_diff_paper
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-06T18:44:11.212208+00:00
-- url     : https://prove2.me/theorems/c7d1b8c8-c78d-4038-a5ab-799a352b023f
-- title:
--   Lemma A.2 — differentiation along shrinking cubes
-- statement:
--   **Lemma A.2 exactly as the source states it.**
--
--   For $\varphi : \mathbb{R}^d \to \mathbb{R}$ locally integrable, for almost every $s$: if $(x_h)_{h>0}$ is a family of points with $x_h \in h\mathbb{Z}^d$ and $s \in \tilde A_h(x_h)$ for every $h > 0$, then
--
--   $$\frac{1}{\lambda_d(A_h(x_h))}\int_{A_h(x_h)} \varphi \;\longrightarrow\; \varphi(s) \qquad (h \to 0^+).$$
--
--   Here $A_h(u) = \{x : \lVert x-u\rVert_\infty < h/2\}$ is the **open** cube of Definition 2.5 and $\tilde A_h(u) = \prod_i [u_i - h/2,\, u_i + h/2)$ the **half-closed** one. The source's Lemma A.2 uses both: the hypothesis is stated for $\tilde A_h$, the average for $A_h$.
--
--   This development's own version, `QFS.lemma_lebesgue_diff`, uses the **closed** cube for both. Since $\tilde A_h(u) \subseteq \overline A_h(u)$, assuming only $s \in \overline A_h(u)$ is a *weaker* hypothesis, so that version is strictly stronger and implies this one; it is also stated over an arbitrary filter and index type rather than along $h \to 0^+$. This theorem records the source's own statement so that what the paper claims is on the platform in the form the paper claims it.
--
--   **Formalization Note** The three cubes differ by a null set, so the averages coincide; only the membership hypothesis is genuinely affected by the choice. The derivation from `QFS.lemma_lebesgue_diff` transports along the subtype of positive reals, since that theorem requires positivity of *every* index and so cannot be instantiated at $\mathbb{R}$ with the $h \to 0^+$ filter directly. The lattice hypothesis $x_h \in h\mathbb{Z}^d$ is carried faithfully from the source but is not used in the proof.
-- source:
--   https://github.com/dbenbenn/quadratic-forms-sobolev/blob/7a1a680db2124d46ce370c91fd450aa454edf491/QuadraticFormsSobolev/LebesgueDiff.lean#L185-L192

import Definitions.Def_QFS_Cubes
import Definitions.Def_QFS_Section3
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Real Set Metric MeasureTheory ENNReal Filter Topology

theorem QFS.lemma_lebesgue_diff_paper {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : LocallyIntegrable φ volume) :
    ∀ᵐ s : EuclideanSpace ℝ (Fin d),
      ∀ x : ℝ → EuclideanSpace ℝ (Fin d),
        (∀ h : ℝ, 0 < h → x h ∈ QFS.scaledLattice d h) →
        (∀ h : ℝ, 0 < h → s ∈ QFS.halfClosedCube h (x h)) →
        Tendsto (fun h => ⨍ y in QFS.cube h (x h), φ y) (𝓝[>] (0:ℝ)) (𝓝 (φ s)) := by sorry
