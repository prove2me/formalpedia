-- Prove2me | Theorems.Thm_RandModSubsetSum_eq_41
-- name    : RandModSubsetSum.eq_41
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:03:34.442698+00:00
-- url     : https://prove2.me/theorems/586cc37f-d203-4006-8176-63a6b2bd05fc
-- title:
--   Equation (41) — the paper's parameters satisfy the hypotheses of Lemma 4.3 with $\gamma=0.000001000026$
-- statement:
--   Take the weights $w_r=W_r/10^{20}$ of Table 4, the nominal kernels built from the Gaussian numerators of Tables 2–4 by (37)–(38), the rates $K_1,\dots,K_7$ of Table 5, and $\gamma=0.000001000026$. For every $\rho\in\mathbb R^{13}$ with $|\rho_r-1/2|\le10^{-10}$ in every stratum,
--
--   $$E_{a,b}-aK_1-bK_2\ge\gamma\quad\big((a,b)\in\{(0,1),(0,2),(1,0),(1,1),(1,2)\}\big),\qquad D_j-K_{j+1}\ge\gamma\quad(j=2,\dots,6),$$
--
--   where $E_{a,b}$ and $D_j$ are the nominal quantities at $\rho$. These are the hypotheses of Lemma 4.3 for every nearly balanced root. The smallest gaps are $D_2-K_3$ and $E_{1,2}-K_1-2K_2$ (Table 8).
--
--   **Formalization Note** The paper certifies Table 8 by outward-rounded interval arithmetic over all allowed root counts; the statement is the inequality itself, for every $\rho$ in the box (p. 44: "The uniform bounds hold for every $\rho_r$ satisfying $|\rho_r-1/2|\le10^{-10}$").
--
--   Differences from the source:
--   - generalization: the hypotheses of Lemma 4.3 for the allowed roots, ρ_r = h_r/n_r with |ρ_r − 1/2| ≤ 10⁻¹⁰ → every real ρ in the box |ρ_r − 1/2| ≤ 10⁻¹⁰; reason: contains every ρ(x) of a nearly balanced root
--   - encoding: E_{a,b} − aK₁ − bK₂ ≥ γ for the five profiles → the inequality for every nonzero observation space S ≤ F₇³ with (a, b) = (b₁(S), b₂(S)); reason: a minimum is ≥ a bound iff every term is
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), (41) and Table 8, pp. 48–49; parameters §6.1–6.2, pp. 41–44

import Mathlib
import Definitions.Def_RandModSubsetSum_Strata
import Definitions.Def_RandModSubsetSum_Kernels
import Definitions.Def_RandModSubsetSum_PaperParams

open scoped BigOperators

namespace RandModSubsetSum

/-- **Equation (41)** (the paper's parameters satisfy the hypotheses of Lemma 4.3, Table 8). Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89),
(41) and Table 8, pp. 48–49; parameters §6.1–6.2, pp. 41–44.

For the stratum weights `w_r = W_r/10²⁰` (Table 4), the nominal kernels built from Tables 2–4 by
(37)–(38), and the rates `K_1, …, K_7` of Table 5, with `γ = 0.000001000026`: for every
`ρ ∈ ℝ^{13}` with `|ρ_r − 1/2| ≤ 10⁻¹⁰` in every stratum,
`E_{a,b} − a K_1 − b K_2 ≥ γ` for the five profiles `(a, b)`, and `D_j − K_{j+1} ≥ γ` for
`j = 2, …, 6`.

**Formalization Note.** The nominal quantities are computed at `ρ` by the recursion (39) (p. 44:
"The uniform bounds hold for every `ρ_r` satisfying `|ρ_r − 1/2| ≤ 10⁻¹⁰`"); the profile
inequalities are stated for every nonzero observation space `S ≤ F₇³`, which is equivalent to the
inequality for each minimum `E_{a,b}` in (9). `paperK i` is `K_{i+1}`. -/
theorem eq_41 (ρ : Fin 13 → ℝ) (hρ : ∀ r, |ρ r - 1 / 2| ≤ 1 / 10 ^ 10) :
    (∀ S : ObsSpace, S ≠ ⊥ →
      paperGamma ≤ obsEntropy paperWeight paperKernel ρ S - ((b1 S : ℝ) * paperK 0 + (b2 S : ℝ) * paperK 1)) ∧
    (∀ j : Fin 7, 2 ≤ j.val → paperGamma ≤ Drate paperWeight paperKernel ρ j.val - paperK j) := by sorry

end RandModSubsetSum
