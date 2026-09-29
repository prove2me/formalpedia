-- Prove2me | Theorems.Thm_RobustMDP_FiniteHorizon_supportFunction_monotone
-- name    : RobustMDP.FiniteHorizon.supportFunction_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:19:23.563034+00:00
-- url     : https://prove2.me/theorems/e971742a-f273-4883-af38-15dd8a309e14
-- title:
--   Proof of Theorem 1, p. 783 — the support function of a set of probability vectors is nondecreasing
-- statement:
--   Let $\mathcal P\subseteq\Delta_n$ be a nonempty set of probability vectors in $\mathbb R^n$. Then its support function is componentwise nondecreasing: for all $u,v\in\mathbb R^n$,
--
--   $$
--   u\le v\ \text{componentwise}\quad\Longrightarrow\quad \sigma_{\mathcal P}(u)\le\sigma_{\mathcal P}(v).
--   $$
--
--   This is the property of the sets $\mathcal P_i^a$ that the proof of Theorem 1 uses: it makes the constraint maps of problems (15) and (16) monotone, so that Lemma 1 applies. No convexity or closedness of $\mathcal P$ is needed.
--
--   **Formalization Note** $\sigma_{\mathcal P}$ is the real `sSup`; nonemptiness and inclusion in $\Delta_n$ make it the true supremum.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 783, proof of Theorem 1 ("Because the sets 𝒫_i^a are all included in Δ^n, the above functions are componentwise nondecreasing")

import Mathlib
import Definitions.Def_RobustMDP_Shared_supportFunction

namespace RobustMDP.FiniteHorizon

/-- (p. 783, proof of Theorem 1.) For a nonempty set `S` of probability vectors in `ℝⁿ`, the
support function `σ_S(v) = sup {pᵀ v : p ∈ S}` is componentwise nondecreasing:
`u ≤ v` componentwise implies `σ_S(u) ≤ σ_S(v)`. -/
theorem supportFunction_monotone {n : ℕ} (S : Set (Fin n → ℝ))
    (hS : S ⊆ stdSimplex ℝ (Fin n)) (hne : S.Nonempty) :
    Monotone (Shared.supportFunction S) := by sorry

end RobustMDP.FiniteHorizon
