-- Prove2me | Theorems.Thm_QFS_cor_rescaled_kernel
-- name    : QFS.cor_rescaled_kernel
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-06T19:12:08.743377+00:00
-- url     : https://prove2.me/theorems/d28eed45-76b4-4553-9054-812c1bef38ca
-- title:
--   Corollary 3.6, weakened — the constant allowed to depend on the configuration and the kernel
-- statement:
--   **Corollary 3.6 of Bux–Kassmann–Schulze with the constant's existential moved inward** —
--   the literal reading of the corollary's own sentence, which is weaker than what the source
--   actually proves. The faithful statement is `QFS.cor_rescaled_kernel_uniform`; this one is
--   derived from it.
--
--   Fix $d \ge 2$, an apex angle $0 < \vartheta \le \pi/2$ and an exponent $0 < \alpha \le 2$.
--   Then there is an angle $\theta' \in (0, \pi/2]$ such that: for every $\vartheta$-bounded
--   configuration $\Gamma$ satisfying `CondMeas`, every $\Lambda$ and every kernel $k$
--   obeying the two-sided bounds (2) of the source with that $\Lambda$, there is a constant
--   $C > 0$ such that for every spacing $h > 0$ there is a configuration $\Gamma'$ whose
--   cones all have apex angle exactly $\theta'$, and for all $x, y \in h\mathbb{Z}^d$ with
--   $\lVert x - y\rVert > \sqrt d\, h$,
--
--   $$\frac{1}{C}\Bigl(\mathbf 1[y \in V^{\Gamma'}\![x]] + \mathbf 1[x \in V^{\Gamma'}\![y]]\Bigr)\lVert x-y\rVert^{-d-\alpha}
--   \;\le\; \omega^k_h(x,y) \;\le\; C\,\lVert x-y\rVert^{-d-\alpha},$$
--
--   where $\omega^k_h(x,y) = h^{-2d}\int_{A_h(x)\times A_h(y)} k$ is the average of $k$ over
--   the two open cubes of edge $h$ at the two lattice points.
--
--   **Why this is the weaker form.** The corollary's sentence reads "Let $k$ ... satisfying
--   (2) for a $\vartheta$-admissible configuration $\Gamma$. Then there are $\vartheta' > 0$
--   and $C > 0$ ...", which taken alone would let $C$ depend on $\Gamma$ and $k$ — the order
--   used here. But the source's Proposition 3.5, which the corollary's proof invokes, declares
--   its constant as $C = C(d,\vartheta)$ and adds "There is no further dependence on $\Gamma$";
--   and the corollary obtains $C$ precisely by applying 3.5 to $\Gamma^h$ and $k^h$, whose apex
--   infimum is the same $\vartheta$ for every $h$. That is exactly how the source gets
--   independence of $h$. So the source's $C$ is uniform in $\Gamma$, $k$ and $h$ together, and
--   depends only on $d$, $\vartheta$, $\alpha$ and $\Lambda$ — which is
--   `QFS.cor_rescaled_kernel_uniform`. This statement is that one with the existential for $C$
--   pushed past $\Gamma$ and $k$, and is implied by it.
--
--   **What is stronger here than in the source's sentence.** $\theta'$ is still produced before
--   $\Gamma$ — which matches the source, since 3.5 pins $\vartheta'$ to $\vartheta$ alone. And
--   every cone of $\Gamma'$ has apex angle *equal* to $\theta'$, where the source asks only that
--   the infimum of the apex angles equal $\vartheta'$.
--
--   **What is weaker.** `CondMeas` — measurability of the sets $\{x : V \subseteq \Gamma(x)\}$ —
--   is carried as an explicit hypothesis. The source derives it from its condition (M) by quoting
--   Debreu's measurable-selection theorem, which is not formalised here. The restriction to
--   $d \ge 2$ is inherited from Lemma 3.3. Measurability of $k$ is not assumed and is not used. Symmetry **is** assumed: it is a field of
--   `QFS.KernelBounds`, the formalisation of assumption (2), and the source's own sentence reads
--   "a symmetric and measurable function satisfying (2)" — so symmetry arrives with (2), and only
--   measurability is dropped.
--
--   The separation threshold $\sqrt d\, h$ is the Euclidean diameter of a cube of edge $h$, so the
--   two cubes are disjoint: nearest neighbours and the diagonal are excluded outright. Nothing
--   relates $\Gamma'$ to $\Gamma$, and the upper bound does not mention $\Gamma'$ at all.
-- source:
--   https://github.com/dbenbenn/quadratic-forms-sobolev/blob/7a1a680db2124d46ce370c91fd450aa454edf491/QuadraticFormsSobolev/Section3Kernel.lean#L749-L770

import Definitions.Def_QFS_Translate
import Definitions.Def_QFS_Defs
import Definitions.Def_QFS_ConeGap
import Definitions.Def_QFS_RefCones
import Definitions.Def_QFS_Section4
import Definitions.Def_QFS_Cubes
import Definitions.Def_QFS_Section3
import Definitions.Def_QFS_Section5
import Definitions.Def_QFS_Section1
import Definitions.Def_QFS_ThinCones
import Definitions.Def_QFS_Section3Kernel
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Real Set Metric MeasureTheory ENNReal

open QFS

variable {d : ℕ}

theorem QFS.cor_rescaled_kernel {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) (hd : 2 ≤ d)
    {α : ℝ} (hα : 0 < α) (hα2 : α ≤ 2) :
    ∃ θ' : ℝ, 0 < θ' ∧ θ' ≤ π / 2 ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ (Λ : ℝ) (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
        KernelBounds Γ α Λ k →
      ∃ C : ℝ, 0 < C ∧
      ∀ h : ℝ, 0 < h →
      ∃ Γ' : Configuration (EuclideanSpace ℝ (Fin d)),
        (∀ u, (Γ' u).apex = θ') ∧ IsBounded Γ' θ' ∧
        ∀ x ∈ scaledLattice d h, ∀ y ∈ scaledLattice d h, Real.sqrt d * h < ‖x - y‖ →
          ENNReal.ofReal C⁻¹ *
              ((indE (coneAt Γ' x) y + indE (coneAt Γ' y) x) * jumpKernel d α x y)
            ≤ discreteKernel d k h x y ∧
          discreteKernel d k h x y ≤ ENNReal.ofReal C * jumpKernel d α x y := by sorry
