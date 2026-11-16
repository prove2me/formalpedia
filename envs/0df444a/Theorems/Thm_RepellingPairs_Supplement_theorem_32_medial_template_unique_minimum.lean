-- Prove2me | Theorems.Thm_RepellingPairs_Supplement_theorem_32_medial_template_unique_minimum
-- name    : RepellingPairs.Supplement.theorem_32_medial_template_unique_minimum
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:59:30.347139+00:00
-- url     : https://prove2.me/theorems/35d20443-d3e6-495b-a5cb-feeadc849466
-- title:
--   Theorem 32 — the medial template $\Phi(D)$ is the unique feasible template of minimum crossing number
-- statement:
--   Let $D$ be an OS (Kalmanson) metric on terminals $0,\dots,k-1$ in this cyclic order, let $X=\{x_0,\dots,x_{2k-1}\}$ be the terminals together with one reference point between each two consecutive terminals, and let $Z=\{z_0,\dots,z_{2k-1}\}$ be boundary points alternating with $X$, $z_i$ lying between $x_{i-1}$ and $x_i$. A **template** is a perfect matching $\Phi$ on $Z$, drawn as chords; $\mathrm{dist}_\Phi(x,y)$ is the number of its chords crossing the $x$–$y$ boundary cut and $\mathrm{cr}(\Phi)$ its number of crossing pairs of chords. A template is **feasible** if
--
--   $$
--   \mathrm{dist}_\Phi(x,y)\ \ge\ b_{x,y}\qquad\text{for all }x,y\in X,
--   $$
--
--   with $b_{x,y}$ the cut bounds built from the repelling numbers of $D$. Let $\Phi(D)$ be the template with $\mathrm{dist}_{\Phi(D)}(x,y)=b_{x,y}$ for all $x,y\in X$ (Lemma 31 of the paper says that it exists and is unique).
--
--   **Theorem.** $\Phi(D)$ is the unique template of minimum crossing number among the feasible templates: every feasible template $\Phi\ne\Phi(D)$ satisfies
--
--   $$
--   \mathrm{cr}(\Phi)>\mathrm{cr}(\Phi(D)).
--   $$
--
--   By Lemma 33 of the paper, $\mathrm{cr}(\Phi(D))$ is then the number of edges of a minimum OS realization of $D$.
--
--   **Formalization Note** The statement asserts that a template $\Phi_0$ with $\mathrm{dist}_{\Phi_0}=b$ on all of $X\times X$ exists and is the only one, and that every feasible $\Phi\ne\Phi_0$ has $\mathrm{cr}(\Phi)>\mathrm{cr}(\Phi_0)$. Points of $X$ and $Z$ are $\mathrm{Fin}(2k)$, $x_i$ is the bar between $z_i$ and $z_{i+1}$ (the base mission's `Config.dist`), and $x_i$ is a terminal iff $i$ is even. All pairs $x,y$ are quantified, $x=y$ included.
--
--   Differences from the source:
--   - encoding: $\Phi(D)$, "the template given by Lemma 31" → the conclusion asserts the existence and uniqueness of a template $\Phi_0$ with $\mathrm{dist}_{\Phi_0}=b$ and states the claim for it; reason: the definite description is unfolded so that the theorem is not vacuous when no such template exists; same content
--   - encoding: $X=\{x_1,\dots,x_m\}$ and $Z=\{z_1,\dots,z_m\}$ with unspecified terminal positions → $\mathrm{Fin}(2k)$ with terminal $t$ at $x_{2t}$ and $x_i$ between $z_i$ and $z_{i+1}$; reason: a labelling of the same points
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), Theorem 32, p.34 (PDF p.35), §5.3.3; X, Z, templates, cr p.31; a_{x,y}, b_{x,y} p.32

import Mathlib
import Definitions.Def_RepellingPairs_IsMetric
import Definitions.Def_RepellingPairs_IsKalmanson
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_PerfectMatching
import Definitions.Def_RepellingPairs_Supplement_cutBound
import Definitions.Def_RepellingPairs_Supplement_crossingNumber

set_option autoImplicit false

namespace RepellingPairs

namespace Supplement

/-- **Theorem 32.** For every OS metric `D` on `k` terminals, the medial template `Φ(D)` is the unique
template of minimum crossing number among the templates `Φ` with `dist_Φ(x, y) ≥ b_{x,y}` for all
`x, y ∈ X`: every other feasible template `Φ ≠ Φ(D)` has `cr(Φ) > cr(Φ(D))`.
Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23,
2026), Theorem 32, p.34 (§5.3.3).

**Formalization Note.** "OS metric" is `IsMetric D ∧ IsKalmanson D` for the cyclic order of `Fin k`. A
template is a perfect matching on the `2k` points `Z = Fin (2k)`, and `dist_Φ(x_i, x_j)` is
`(Φ.config).dist i j`, the point `x_i` of `X` being the bar between `z_i` and `z_{i+1}`; `x_i` is a
terminal iff `i` is even. `Φ(D)` is "the template given by Lemma 31", the unique template with
`dist_Φ = b` on all of `X × X`; the statement asserts that such a template `Φ₀` exists and is unique, and
then Theorem 32's claim about it. All pairs `x, y`, including `x = y`, are quantified. -/
theorem theorem_32_medial_template_unique_minimum {k : ℕ} (D : Fin k → Fin k → ℝ)
    (hD : IsMetric D) (hK : IsKalmanson D) :
    ∃ Φ₀ : PerfectMatching (2 * k),
      (∀ i j, ((Φ₀.config.dist i j : ℕ) : ℤ) = cutBound D i j) ∧
      (∀ Φ : PerfectMatching (2 * k), (∀ i j, ((Φ.config.dist i j : ℕ) : ℤ) = cutBound D i j) →
        Φ = Φ₀) ∧
      ∀ Φ : PerfectMatching (2 * k), (∀ i j, cutBound D i j ≤ ((Φ.config.dist i j : ℕ) : ℤ)) →
        Φ ≠ Φ₀ → crossingNumber Φ₀ < crossingNumber Φ := by sorry

end Supplement

end RepellingPairs
