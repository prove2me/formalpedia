-- Prove2me | Theorems.Thm_ProcessingNetworks_FluidStability_uniform_slln_service_completions
-- name    : ProcessingNetworks.FluidStability.uniform_slln_service_completions
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T17:36:30.063986+00:00
-- url     : https://prove2.me/theorems/1ff5510b-4fec-40f1-ab07-ced31cd488b8
-- title:
--   Lemma 6.9 — a uniform SLLN for the delayed random walk
-- statement:
--   **Lemma 6.9.** For a sample point $\omega$ at which the SLLN (2.15) for service times holds
--   (i.e. $\frac{1}{n}\sum_{\ell \le n} v_j(\ell,\omega) \to m_j$), for each activity $j$,
--   $$
--   \lim_{n \to \infty} \sup_{x \in \mathcal X} \left| \frac{1}{n} V^x_j(n,\omega) - m_j \right| = 0,
--   $$
--   where $V^x_j(n,\omega)$ is the "delayed random walk" of Eq. (6.47): the sum of the residual
--   service times of the (at most $N^x_j(0)$) type-$j$ services already open at initial state
--   $x$, plus enough of the post-time-zero service times $v_j(1), v_j(2), \dots$ to reach a total
--   of $n$ terms.
--
--   The content of the lemma is that the ordinary SLLN for $v_j$, which only handles the
--   "post-time-zero" segment of $V^x_j$, extends to hold *uniformly* over every initial state $x$
--   — the $x$-dependent delay from the (at most $N^x_j(0) \le \kappa$, a fixed constant) residual
--   initial service times becomes negligible as $n \to \infty$, uniformly in $x$. This is the key
--   input to Lemma 6.8's proof.
--
--   **Formalization note.** "$\lim_n \sup_x |\cdots| = 0$" is formalized directly by its
--   $\varepsilon$-$N$ meaning (`∀ ε > 0, ∃ Nb, ∀ n ≥ Nb, ∀ x, |...| < ε`) rather than via a Lean
--   sup expression: since `Xstate` may be countably infinite, an explicit `⨆ x, ...` over `ℝ`
--   would fall back to a junk value of `0` if the family were not bounded above, which would risk
--   silently trivializing the statement. The $\varepsilon$-$N$ form has no such risk and is
--   exactly what "sup $\to 0$" means. Uniformity in $x$ rests on the standard setup's finite pool
--   $\Pi_0$ (the stochastic bound (6.36)) and the uniform bound (6.35) on $N^x_j(0)$, both fields of
--   `SPNProcessFamily`.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 119, Lemma 6.9

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_FluidStability_FluidEquationData
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidStability_SPNProcessFamily

namespace ProcessingNetworks.FluidStability

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability

/-- Lemma 6.9, Dai & Harrison p. 119 (PDF p. 135): for `ω` at which the SLLN (2.15) for service
times holds, `lim_{n→∞} sup_{x∈𝒳} |(1/n) V^x_j(n,ω) − m_j| = 0` (6.48), formalized directly by
its `ε`-`Nb` meaning (a supremum over the possibly countably infinite state space `Xstate` is
not itself asserted to be a real number by this statement, only that it is eventually smaller
than every `ε > 0`, uniformly over every state). -/
theorem uniform_slln_service_completions
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ} (fam : SPNProcessFamily Mrep sd dat E v φ) (ω : Ω)
    (h215 :
      ∀ j, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop (nhds (dat.m j)))
    (j : Fin J) :
    ∀ ε : ℝ, 0 < ε → ∃ Nb : ℕ, ∀ n ≥ Nb, ∀ x : Xstate,
      |(n : ℝ)⁻¹ * spnV fam x j n ω - dat.m j| < ε := by sorry

end ProcessingNetworks.FluidStability
