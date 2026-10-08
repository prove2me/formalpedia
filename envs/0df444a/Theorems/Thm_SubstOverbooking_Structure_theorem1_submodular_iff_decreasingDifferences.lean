-- Prove2me | Theorems.Thm_SubstOverbooking_Structure_theorem1_submodular_iff_decreasingDifferences
-- name    : SubstOverbooking.Structure.theorem1_submodular_iff_decreasingDifferences
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:57.751162+00:00
-- url     : https://prove2.me/theorems/5ebdf6c0-243d-4533-aabd-2b5dcdd373b5
-- title:
--   Theorem 1, p. 87 — on a product of subsets of ℝ, f is submodular iff f has decreasing differences
-- statement:
--   Let $T_1, \dots, T_n \subseteq \mathbb R$ and $S = T_1 \times \dots \times T_n \subseteq \mathbb R^n$, and let $f : \mathbb R^n \to \mathbb R$. Then $f$ is submodular on $S$, i.e.
--
--   $$f(s \vee s') + f(s \wedge s') \le f(s) + f(s') \qquad (s, s' \in S),$$
--
--   if and only if $f$ has decreasing differences on $S$ in the sense of Definition 1.
--
--   This equivalence, quoted by the paper from Sundaram (1996), is what turns the pairwise inequality (7) into submodularity of the expected net revenue.
--
--   **Formalization Note.** The paper states the theorem for an arbitrary $S \subset \mathbb R^n$. As printed it is false: on $S = \{(0, 1), (1, 0)\}$ decreasing differences holds trivially (only zero increments stay in $S$), while the lattice inequality compares $f(1,1) + f(0,0)$ with $f(0,1) + f(1,0)$ and fails for suitable $f$. The statement is therefore made for product sets $S$, which covers every set the paper applies it to ($\mathbb R^n_{\ge 0}$ and $P^n$). Submodularity of $f$ is supermodularity of $-f$ (platform `SupermodularOn`).
-- source:
--   Karaesmen & van Ryzin, Overbooking with Substitutable Inventory Classes, Operations Research 52(1):83–104 (2004), p. 87, Theorem 1 (after Sundaram 1996)

import Mathlib
import Definitions.Def_SubstOverbooking_Structure_Setting
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

namespace SubstOverbooking.Structure

theorem theorem1_submodular_iff_decreasingDifferences {n : ℕ} (T : Fin n → Set ℝ)
    (f : (Fin n → ℝ) → ℝ) :
    Supermodularity.Monotonicity.SupermodularOn (fun s => - f s) (Set.pi Set.univ T) ↔
      DecreasingDifferencesOn f (Set.pi Set.univ T) := by sorry

end SubstOverbooking.Structure
