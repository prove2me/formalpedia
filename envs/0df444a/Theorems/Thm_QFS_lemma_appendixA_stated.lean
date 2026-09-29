-- Prove2me | Theorems.Thm_QFS_lemma_appendixA_stated
-- name    : QFS.lemma_appendixA_stated
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-07T08:41:50.898147+00:00
-- url     : https://prove2.me/theorems/df0b346c-c333-4384-8649-99df5c144fce
-- title:
--   Lemma A.1 — the domain conclusion, the ball clause, and the scaling remark
-- statement:
--   **Lemma A.1 of Bux–Kassmann–Schulze, with the three assertions it makes for a fixed $\alpha$.**
--
--   Fix $\alpha$, $\kappa \ge 1$, $c_0 \ge 1$, a kernel $k$ and a function $f$, and assume the
--   **ball comparability hypothesis**: for every ball $B = B_S(y_0)$ and every $f$ square-integrable
--   on $B^* = B_{\kappa S}(y_0)$,
--
--   $$\lvert f\rvert^2_{H^{\alpha/2}(B)} \;\le\; c_0\,\mathcal E_{B^*}[k,f].$$
--
--   Then, writing $c(W) = W.\mathrm{dydaConst}/(c_0\,W.\mathrm{overlapBound})$:
--
--   1. **for every measurable $\Omega$ with a Whitney family $W$**, and every $f \in L^2(\Omega)$,
--      $c(W)\,\lvert f\rvert^2_{H^{\alpha/2}(\Omega)} \le \mathcal E_{\Omega}[k,f]$;
--   2. **for every Whitney family for balls $W$**, the same on *every* ball $B_R(x_0)$ with one and
--      the same $c(W)$ — independent of $x_0$ and $R$;
--   3. **for every $a > 0$**, the inequality on the dilate $a\cdot\Omega$ holds with *literally the
--      same* $c(W)$ as on $\Omega$.
--
--   **These are the source's own three sentences.** The conclusion is claim 1, with
--   $\tilde c = \tilde c(d,\kappa,\alpha,\Omega)$ allowed to depend on the domain. Then: "The
--   constant $\tilde c$ depends on the domain $\Omega$ only up to scaling" — claim 3. "In
--   particular, if $\Omega$ is a ball, the constant can be chosen independently of $\Omega$" —
--   claim 2. None of the three implies another: claim 1's constant comes from a family attached to
--   the single $\Omega$, and the difference is visible in the types, `QFS.WhitneyDomainData` being
--   indexed by $\Omega$ where `QFS.WhitneyBallData` carries one overlap bound and one Dyda constant
--   for every ball at once.
--
--   **Claim 3 is not free.** It rests on `QFS.WhitneyDomainData.smul`, which transports a Whitney
--   family along a dilation with its overlap bound and Dyda constant unchanged, and that in turn on
--   a change of variables for the Gagliardo seminorm: dilating the domain by $a$ multiplies
--   $\lvert\cdot\rvert^2_{H^{\alpha/2}}$ by $a^{d-\alpha}$ once the function is precomposed. Both
--   sides of Dyda's inequality pick up the same factor, which is why the constant survives.
--
--   **The lemma's fourth assertion is stated separately.** "For $0 < \alpha_0 \le \alpha < 2$, the
--   constant $\tilde c$ depends on $\alpha_0$ but not on $\alpha$" is
--   `QFS.lemma_appendixA_alpha_uniform`. It is not a conjunct here because it needs a Whitney family
--   for *every* $\alpha$ in the range sharing one overlap bound and one Dyda constant; requiring
--   that would burden the three claims above with a hypothesis the source does not ask of them.
--
--   **Both quoted inputs are hypotheses, not theorems.** The source's proof quotes the Whitney
--   decomposition for properties (i)–(iii) and [Dyda06] for inequality (13), and proves neither.
--   Both are fields of $W$ here. That such a family exists for balls is `QFS.exists_whitneyBallData`,
--   an `Open` target of this mission. **Lipschitz regularity of $\Omega$ is not assumed**, only
--   measurability — it enters the source solely through the Whitney decomposition.
--
--   `QFS.lemma_appendixA` is claims 1 and 2 alone.
-- source:
--   https://github.com/dbenbenn/quadratic-forms-sobolev/blob/c21c00974c7ee792c796523d51f0ecfa12e6fb2d/QuadraticFormsSobolev/AppendixA.lean#L567

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
import Definitions.Def_QFS_LebesgueDiff
import Definitions.Def_QFS_LebesgueDiff2
import Definitions.Def_QFS_Renormalization
import Definitions.Def_QFS_FirstJump
import Definitions.Def_QFS_Assembly
import Definitions.Def_QFS_PathAssembly
import Definitions.Def_QFS_BlockPaths
import Definitions.Def_QFS_Section6
import Definitions.Def_QFS_Rescaling
import Definitions.Def_QFS_Section32
import Definitions.Def_QFS_AppendixA
import Definitions.Def_QFS_FavoredGraph
import Definitions.Def_QFS_Indicator
import Definitions.Def_QFS_WhitneyDomain
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Appendix A: the auxiliary lemmas

The paper's `\appendix` prints as Appendix A, with Lemmas A.1 and A.2.

**The chain (18) inside Lemma A.1.** Lemma A.1 passes from balls to a bounded
Lipschitz domain using a Whitney family and Dyda's inequality (13), both quoted
rather than proved. The one step the paper carries out itself is the
finite-overlap estimate, and it is proved here
(`tsum_setLIntegral_le_of_overlap`); `lemma_ball_to_domain` then assembles the
whole chain with the two quoted inputs as explicit hypotheses.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

open QFS

variable {d : ℕ}

theorem QFS.lemma_appendixA_stated {α κ c₀ : ℝ} (hc₀ : 1 ≤ c₀)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (H : ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (S : ℝ), 0 < S →
      MemLp f 2 (volume.restrict (ball y₀ (κ * S))) →
      formHs (ball y₀ S) α f ≤ ENNReal.ofReal c₀ * form (ball y₀ (κ * S)) k f)
    (hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    (∀ Ω : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet Ω →
        ∀ W : WhitneyDomainData d α κ Ω, MemLp f 2 (volume.restrict Ω) →
        ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ)) * formHs Ω α f
          ≤ form Ω k f)
      ∧ (∀ W : WhitneyBallData d α κ,
        ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
        MemLp f 2 (volume.restrict (ball x₀ R)) →
        ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ)) * formHs (ball x₀ R) α f
          ≤ form (ball x₀ R) k f)
      ∧ (∀ Ω : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet Ω →
        ∀ W : WhitneyDomainData d α κ Ω, ∀ a : ℝ, 0 < a →
        MemLp f 2 (volume.restrict ((a • ·) '' Ω)) →
        ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ))
            * formHs ((a • ·) '' Ω) α f
          ≤ form ((a • ·) '' Ω) k f) := by sorry
