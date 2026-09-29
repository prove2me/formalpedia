-- Prove2me | Theorems.Thm_QFS_lemma_appendixA_alpha_uniform
-- name    : QFS.lemma_appendixA_alpha_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-07T08:39:28.304432+00:00
-- url     : https://prove2.me/theorems/ab1567d3-d0c0-46ad-b22b-3a9908f65d7a
-- title:
--   Lemma A.1's constant depends on α only through a lower bound α₀
-- statement:
--   **"For $0 < \alpha_0 \le \alpha < 2$, the constant $\tilde c$ depends on $\alpha_0$ but not on
--   $\alpha$"** — the last sentence of Lemma A.1 of Bux–Kassmann–Schulze.
--
--   Suppose the Whitney family for $\Omega$ can be chosen, for **every** $\alpha \in [\alpha_0, 2)$,
--   with one and the same overlap bound $M$ and one and the same Dyda constant $\gamma$, and suppose
--   the ball comparability hypothesis holds throughout that range with one $c_0$. Then Lemma A.1's
--   conclusion holds for every such $\alpha$ with the single constant
--
--   $$\frac{\gamma}{c_0\,M},$$
--
--   which does not mention $\alpha$.
--
--   **This is a transfer, not a strengthening, and deliberately so.** The $\alpha$-dependence of the
--   constant sits entirely in Dyda's inequality (13), which the source quotes from [Dyda06] and this
--   development carries as a hypothesis rather than proving. The overlap bound is purely geometric
--   and $\alpha$-free, but the Dyda constant is not ours to control — so uniformity over
--   $[\alpha_0, 2)$ is a property *of the quoted input*, and this statement says exactly that if the
--   input has it, so does the conclusion. That is the same epistemic status the source's own sentence
--   has: a remark about what the quoted decomposition delivers.
--
--   $\alpha_0$ enters only by delimiting the range on which the uniform family is assumed, which is
--   why the constant "depends on $\alpha_0$".
--
--   This is Lemma A.1's fourth assertion. The three it makes for a fixed $\alpha$ — the domain
--   conclusion, the "in particular, for a ball" clause, and the scaling remark — are
--   `QFS.lemma_appendixA_stated`. It is not a conjunct there because it needs this family over the
--   whole range, a hypothesis the other three do not require.
-- source:
--   https://github.com/dbenbenn/quadratic-forms-sobolev/blob/c21c00974c7ee792c796523d51f0ecfa12e6fb2d/QuadraticFormsSobolev/AppendixA.lean#L597

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

theorem QFS.lemma_appendixA_alpha_uniform {κ c₀ α₀ γ : ℝ} {M : ℕ} (hc₀ : 1 ≤ c₀)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : MeasurableSet Ω)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (W : ∀ α, α₀ ≤ α → α < 2 → WhitneyDomainData d α κ Ω)
    (hM : ∀ α h₁ h₂, (W α h₁ h₂).overlapBound = M)
    (hγ : ∀ α h₁ h₂, (W α h₁ h₂).dydaConst = γ)
    (H : ∀ α, α₀ ≤ α → α < 2 → ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (S : ℝ), 0 < S →
      MemLp f 2 (volume.restrict (ball y₀ (κ * S))) →
      formHs (ball y₀ S) α f ≤ ENNReal.ofReal c₀ * form (ball y₀ (κ * S)) k f)
    (hf : MemLp f 2 (volume.restrict Ω))
    (hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    ∀ α, α₀ ≤ α → α < 2 →
      ENNReal.ofReal (c₀⁻¹ * γ / (M : ℝ)) * formHs Ω α f ≤ form Ω k f := by sorry
