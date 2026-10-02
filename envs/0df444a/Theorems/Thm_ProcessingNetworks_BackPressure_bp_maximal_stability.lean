-- Prove2me | Theorems.Thm_ProcessingNetworks_BackPressure_bp_maximal_stability
-- name    : ProcessingNetworks.BackPressure.bp_maximal_stability
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T18:59:13.357271+00:00
-- url     : https://prove2.me/theorems/e1b91bf2-2833-49b1-b0a5-9294259e9aa9
-- title:
--   Theorem 9.12 — maximal stability of relaxed back-pressure (goal)
-- statement:
--   This is the goal theorem of the mission — the book's version of the classical max-weight/
--   back-pressure maximal-stability theorem (Tassiulas–Ephremides territory).
--
--   **Theorem 9.12.** Consider a Leontief network operating under relaxed back-pressure control.
--   If the static planning problem's optimal objective value $\gamma^* < 1$, the fluid limit is
--   stable, and hence the network's ambient Markov chain is positive recurrent.
--
--   The proof exhibits a quadratic Lyapunov function $f(t) = \sum_i \hat Z_i(t)^2$ and shows,
--   using the characteristic equation (9.22) directly (not Lemma 9.11's finer $Y$-structure), that
--   $\dot f(t) \le -2\delta\sqrt{f(t)}$ for a constant $\delta>0$ built from Assumption 9.2's
--   witness vector — concluding via Lemma 8.6 (mission V).
--
--   **Formalization note.** The hypothesis is exactly (6.1)-(6.6) plus (9.22)
--   (`IsRelaxedBPFluidSolution`), matching the book's own proof, which never invokes Lemma 9.11's
--   $Y$-decomposition — only the characteristic equation itself. The arrival-rate vector is
--   nonnegative, and the capacity consumption matrix is nonnegative with no zero column (Section
--   2.1), so that the allocation polytope is bounded and $z$-maximal allocations exist. The
--   conclusion is stability of the relaxed-BP fluid model (Definition 6.3 for (6.1)–(6.6) + (9.22)),
--   which is what the Lyapunov proof establishes and which implies fluid limit stability through
--   Theorem 9.8.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 177, Theorem 9.12

import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_LeontiefNetwork
import Definitions.Def_ProcessingNetworks_BackPressure_FluidModelSolution

namespace ProcessingNetworks.BackPressure

/-- Theorem 9.12, Dai & Harrison p. 177 (PDF p. 193) — the goal theorem of this mission: consider
a Leontief network operating under the relaxed back-pressure control policy. If the static
planning problem has optimal objective value `γ* < 1`, then the fluid limit is stable (and hence,
by Theorem 6.2, the network's ambient Markov chain is positive recurrent). The arrival-rate vector
is nonnegative and the capacity consumption matrix nonnegative with no zero column (Section 2.1),
so that the allocation polytope is bounded and `z`-maximal allocations exist. The conclusion is
stability of the relaxed-BP fluid model (Definition 6.3 for (6.1)–(6.6) + (9.22)), which is what
the book's Lyapunov proof establishes and which implies fluid limit stability via Theorem 9.8. -/
theorem bp_maximal_stability
    {I J K : ℕ} (dat : SPNPlanningData I J K) (hleontief : IsLeontiefNetwork dat)
    (hA : ∀ k j, 0 ≤ dat.A k j) (hAcol : ∀ j, ∃ k, 0 < dat.A k j)
    (lam : Fin I → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (γstar : ℝ) (hopt : IsOptimalSPPValue dat lam γstar) (hsub : γstar < 1) :
    RelaxedBPFluidStable dat lam := by sorry

end ProcessingNetworks.BackPressure
