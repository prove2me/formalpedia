-- Prove2me | Theorems.Thm_ProcessingNetworks_Stability_drift_condition_implies_positive_recurrent
-- name    : ProcessingNetworks.Stability.drift_condition_implies_positive_recurrent
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:19:58.301397+00:00
-- url     : https://prove2.me/theorems/62f645cb-ef46-440e-926a-53685adb5929
-- title:
--   Lemma 3.7 — a drift condition sufficient for positive recurrence
-- statement:
--   For a state $x$ of the ambient Markov chain $X$ of a Markov representation
--   (Assumption 3.1), write $|x| := |z| := \sum_{i} z_i$ where $z = f(x)$ (Eq. 3.4), and let
--   $\mathbb{E}_x$ denote expectation under $X(0) = x$.
--
--   **Lemma 3.7.** If there is a $\delta > 0$ such that
--   $$
--   \lim_{|x| \to \infty} \frac{1}{|x|}\, \mathbb{E}_x\big[Z(|x|\delta)\big] = 0, \tag{3.5}
--   $$
--   then the ambient Markov chain $X$ is positive recurrent.
--
--   This is the book's bridge from a fluid-scale drift condition to the probabilistic notion of
--   stability, foreshadowing the whole fluid-model machinery of Chapter 6: the hypothesis says that,
--   started from a state of total size $|x|$, the expected buffer content at the fluid-scaled time
--   $|x|\delta$ is $o(|x|)$ — vanishing relative to the initial size.
--
--   **Formalization note.** $|x|$ is `M.size x` $= \sum_i z_i$ (Eq. 3.4); the limit
--   `Tendsto ... (Filter.comap M.size Filter.atTop) ...` formalizes "as $|x| \to \infty$", taken
--   componentwise in $\mathbb{Z}_+^I$; and $\mathbb{E}_x$ is the expectation under the conditional
--   measure `ℙ[|{ω | M.X 0 ω = x}]`, following the book's own convention $P_x(A) = P(A \mid X(0) = x)$
--   (Definition D.2), with the hypothesis `hsupp` that every state carries positive initial mass so
--   that each $\mathbb{E}_x$ is defined. The expectation is taken as a Lebesgue integral in
--   $[0, \infty]$, so an infinite $\mathbb{E}_x[Z_i(|x|\delta)]$ violates (3.5) as it should, rather
--   than being read as $0$. The conclusion is positive recurrence of the continuous-time chain
--   (Definition D.15, `PositiveRecurrent M.jump M.rate`).
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 48, Lemma 3.7

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions

namespace ProcessingNetworks.Stability

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- Lemma 3.7 (a drift-type sufficient condition for positive recurrence), Dai & Harrison, p. 48:
if there is a `δ > 0` such that, as `|x| → ∞` over states `x` of the ambient chain,
`(1/|x|) E_x[Z(|x|δ)] → 0` componentwise, then the ambient chain is positive recurrent. Here
`M.size x` is the book's `|x| = ∑ᵢ zᵢ` for `f x = (n, z)` (Eq. 3.4), `E_x[·]` is the expectation
under the chain started at `x`, i.e. under `ℙ[|{X(0) = x}]` (every state is given positive
initial mass by `hsupp`, so that these conditional laws are all defined), and the expectation is
the Lebesgue integral in `ℝ≥0∞`, so an infinite expectation counts as such rather than as `0`. -/
theorem drift_condition_implies_positive_recurrent
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    (M : MarkovRepresentation Xstate I J N Z)
    (hsupp : ∀ x : Xstate, ℙ {ω | M.X 0 ω = x} ≠ 0)
    (δ : ℝ) (hδ : 0 < δ)
    (hdrift :
      Tendsto (fun x : Xstate => fun i : Fin I =>
          (∫⁻ ω, ((Z (M.size x * δ) ω i : ℕ) : ℝ≥0∞) ∂(ℙ[|{ω | M.X 0 ω = x}])) /
            ENNReal.ofReal (M.size x))
        (Filter.comap M.size Filter.atTop) (nhds (0 : Fin I → ℝ≥0∞))) :
    PositiveRecurrent M.jump M.rate := by sorry

end ProcessingNetworks.Stability
