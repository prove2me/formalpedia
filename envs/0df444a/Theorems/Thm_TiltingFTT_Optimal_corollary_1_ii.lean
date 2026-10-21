-- Prove2me | Theorems.Thm_TiltingFTT_Optimal_corollary_1_ii
-- name    : TiltingFTT.Optimal.corollary_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:42.450114+00:00
-- url     : https://prove2.me/theorems/23c0a457-6cc3-4dba-8c5e-96624f6eb0b6
-- title:
--   Corollary 1 (ii), p. 27 — a sufficiently high FTT makes the pooling equilibrium impossible
-- statement:
--   Assume the standing assumptions. There is a tax level $\tau_0\ge0$ such that for every $\tau\ge\tau_0$ no pooling equilibrium exists:
--   $$\exists\,\tau_0\ge0\ \ \forall\tau\ge\tau_0\ \ \forall T_P:\ T_P\ \text{is not a pooling equilibrium trade at tax }\tau.$$
--
--   This is the "tilting" property of the FTT: the tax acts on the participation constraint of the informed trader in state $L$ and can rule out the liquid, uninformative equilibrium.
--
--   **Formalization Note.** Item (i) of Corollary 1 is not formalized: as printed it is garbled, and its proof (labelled "(ii)" on p. 46, the labels being swapped) says that only the Pareto-dominant trade $T_L=\bar T_L$ is forced down by the tax, which is already part of Proposition 2.
-- source:
--   Dieler, Biswas, Calzolari & Castiglionesi, Asset Trade, Real Investment and a Tilting Financial Transaction Tax, accepted manuscript of January 24, 2022 (SSRN 2739357; Management Science 69(4), doi:10.1287/mnsc.2022.4417), Corollary 1 (ii), p. 27; proof p. 46

import Mathlib
import Definitions.Def_TiltingFTT_Optimal_Model

namespace TiltingFTT.Optimal

theorem corollary_1_ii (P : Firm) (hS : Standing P) :
    ∃ τ₀ : ℝ, 0 ≤ τ₀ ∧ ∀ τ, τ₀ ≤ τ → ∀ TP, ¬ IsPoolingEq P τ TP := by sorry

end TiltingFTT.Optimal
