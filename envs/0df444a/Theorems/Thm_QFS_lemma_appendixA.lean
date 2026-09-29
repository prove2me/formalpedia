-- Prove2me | Theorems.Thm_QFS_lemma_appendixA
-- name    : QFS.lemma_appendixA
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-07T08:15:41.571008+00:00
-- url     : https://prove2.me/theorems/3616380e-41a3-430e-8546-f50c88f24a59
-- title:
--   Lemma A.1 — the domain conclusion and the ball clause (first two assertions)
-- statement:
--   **Superseded by `QFS.lemma_appendixA_stated`, which is the form this mission's Lemma A.1 milestone links.** That statement adds the source's third assertion — "The constant $\tilde c$ depends on the domain $\Omega$ only up to scaling" — as a further conjunct. This statement, its first two conjuncts, remains true and is one of the inputs to it; it could not be extended in place because a published `formal_statement` is immutable. The fourth assertion, uniformity in $\alpha$ over $[\alpha_0, 2)$, is `QFS.lemma_appendixA_alpha_uniform`.
--
--   ---
--
--   **Lemma A.1 of Bux–Kassmann–Schulze, exactly as the source states it.**
--
--   Fix $\alpha$, $\kappa \ge 1$ and $c_0 \ge 1$, a kernel $k$ and a function $f$, and suppose
--   the **ball comparability hypothesis** holds: for every ball $B = B_S(y_0)$ and every $f$
--   square-integrable on $B^* = B_{\kappa S}(y_0)$,
--
--   $$\lvert f\rvert^2_{H^{\alpha/2}(B)} \;\le\; c_0\,\mathcal E_{B^*}[k,f].$$
--
--   Then **both** of the following hold.
--
--   1. **For every measurable $\Omega$ carrying a Whitney family** $W$ (a `QFS.WhitneyDomainData`
--      for $\Omega$) and every $f \in L^2(\Omega)$,
--      $$\frac{W.\mathrm{dydaConst}}{c_0\, W.\mathrm{overlapBound}}\;\lvert f\rvert^2_{H^{\alpha/2}(\Omega)}
--      \;\le\; \mathcal E_{\Omega}[k,f].$$
--   2. **For every Whitney family for balls** $W$ (a `QFS.WhitneyBallData`), the same inequality
--      holds on *every* ball $B_R(x_0)$, with **one and the same constant** built from that single
--      $W$ — independent of $x_0$ and $R$.
--
--   **Why the conjunction.** The source's conclusion is claim 1, with a constant
--   $\tilde c = \tilde c(d,\kappa,\alpha,\Omega)$ allowed to depend on the domain. The sentence
--   immediately after adds: "The constant $\tilde c$ depends on the domain $\Omega$ only up to
--   scaling. **In particular, if $\Omega$ is a ball, the constant can be chosen independently of
--   $\Omega$.**" That is a uniformity assertion which claim 1 does not give — claim 1's constant
--   comes from a Whitney family attached to the single $\Omega$ — so the lemma as stated is the
--   conjunction of the two. The difference is visible in the types: `WhitneyDomainData` is indexed
--   by $\Omega$, while `WhitneyBallData` carries one overlap bound and one Dyda constant serving
--   every ball at once.
--
--   **The Whitney decomposition and Dyda's inequality are hypotheses, not theorems.** The source's
--   proof opens by quoting the Whitney decomposition technique for properties (i)–(iii) and
--   [Dyda06] for inequality (13); it proves neither. Both are carried here as the fields of $W$, so
--   every consequence declares the dependence in its own type. That a Whitney family exists for
--   balls is `QFS.exists_whitneyBallData`, an `Open` target of this mission.
--
--   **Lipschitz regularity of $\Omega$ is not assumed** — only measurability. It enters the source
--   only through the Whitney decomposition, which is supplied here rather than constructed, so
--   assuming it would be assuming something the proof never uses.
--
--   **Not formalized**: the two remaining sentences about the constant — that $\tilde c$ depends on
--   $\Omega$ only up to scaling, and that for $0 < \alpha_0 \le \alpha < 2$ it depends on $\alpha_0$
--   but not on $\alpha$.
--
--   Proved by pairing `QFS.formHs_le_form_domain` with `QFS.formHs_le_form_of_ballComparability`.
-- source:
--   https://github.com/dbenbenn/quadratic-forms-sobolev/blob/9b0091234843d28030b9cd734fa84b44a083b3a4/QuadraticFormsSobolev/AppendixA.lean#L356-L390

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

theorem QFS.lemma_appendixA {α κ c₀ : ℝ} (hc₀ : 1 ≤ c₀)
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
          ≤ form (ball x₀ R) k f) := by sorry
