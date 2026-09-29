-- Prove2me | Theorems.Thm_QFS_lemma_appendixA_scaling
-- name    : QFS.lemma_appendixA_scaling
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-07T08:37:02.331418+00:00
-- url     : https://prove2.me/theorems/3f45b355-fa01-4807-861d-cfa4e49aa5f3
-- title:
--   Lemma A.1's constant depends on the domain only up to scaling
-- statement:
--   **"The constant $\tilde c$ depends on the domain $\Omega$ only up to scaling"** — the remark
--   following Lemma A.1 of Bux–Kassmann–Schulze.
--
--   Under Lemma A.1's hypotheses, if $\Omega$ is measurable and carries a Whitney family $W$, then
--   for every $a > 0$ the conclusion holds on the dilate $a\cdot\Omega$ with **literally the same
--   constant** $W.\mathrm{dydaConst}/(c_0\,W.\mathrm{overlapBound})$ built from $\Omega$'s own
--   family:
--
--   $$\frac{W.\mathrm{dydaConst}}{c_0\,W.\mathrm{overlapBound}}\;
--   \lvert f\rvert^2_{H^{\alpha/2}(a\cdot\Omega)} \;\le\; \mathcal E_{a\cdot\Omega}[k,f].$$
--
--   Since the same holds with $a^{-1}$, the constants achievable on $\Omega$ and on $a\cdot\Omega$
--   are the same set: the constant is a function of the dilation class of $\Omega$, which is what
--   the source's sentence asserts.
--
--   **How it is proved.** `QFS.WhitneyDomainData.smul` transports a Whitney family along
--   $x \mapsto a x$ — centres scale, radii scale, and properties (ii) and (iii) transport because a
--   dilation is a bijection carrying balls to balls. The one substantive field is Dyda's inequality
--   (13), and it survives because of a change of variables for the Gagliardo seminorm: dilating the
--   domain by $a$ multiplies $\lvert\cdot\rvert^2_{H^{\alpha/2}}$ by exactly $a^{d-\alpha}$ once the
--   function is precomposed with the dilation, so **both sides of (13) acquire the same factor** and
--   the constant is unchanged. That scaling law is new to this formalization — the development had
--   otherwise avoided change of variables for Lebesgue measure, proving §3.2's estimates at scale
--   $h$ directly instead.
--
--   The full statement of Lemma A.1 for a fixed $\alpha$, with this as its third conjunct, is
--   `QFS.lemma_appendixA_stated`.
-- source:
--   https://github.com/dbenbenn/quadratic-forms-sobolev/blob/c21c00974c7ee792c796523d51f0ecfa12e6fb2d/QuadraticFormsSobolev/AppendixA.lean#L539

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

theorem QFS.lemma_appendixA_scaling {α κ c₀ : ℝ} (hc₀ : 1 ≤ c₀)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (H : ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (S : ℝ), 0 < S →
      MemLp f 2 (volume.restrict (ball y₀ (κ * S))) →
      formHs (ball y₀ S) α f ≤ ENNReal.ofReal c₀ * form (ball y₀ (κ * S)) k f)
    (hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : MeasurableSet Ω)
    (W : WhitneyDomainData d α κ Ω) {a : ℝ} (ha : 0 < a)
    (hf : MemLp f 2 (volume.restrict ((a • ·) '' Ω))) :
    ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ)) * formHs ((a • ·) '' Ω) α f
      ≤ form ((a • ·) '' Ω) k f := by sorry
