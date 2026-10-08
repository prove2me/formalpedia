-- Prove2me | Theorems.Thm_SubstOverbooking_Structure_lemma1_V0_submodular
-- name    : SubstOverbooking.Structure.lemma1_V0_submodular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:45.662884+00:00
-- url     : https://prove2.me/theorems/cd0963d8-8154-47a0-9ede-d488f27b8b15
-- title:
--   Lemma 1, p. 87 — V₀(z, c) is submodular in (z₁, …, zₙ)
-- statement:
--   Fix net benefits $a_{ij}$ and capacities $c_j \ge 0$ for $j = 1, \dots, m$. The service-period value $V_0(\cdot, c)$ is submodular on the nonnegative orthant: for all $z, z' \in \mathbb R^n_{\ge 0}$,
--
--   $$V_0(z \vee z', c) + V_0(z \wedge z', c) \le V_0(z, c) + V_0(z', c),$$
--
--   where $\vee, \wedge$ are the componentwise maximum and minimum.
--
--   Submodularity says that the marginal value of one more surviving customer of a class does not increase when more customers of other classes show up: classes compete for the same scarce capacity.
--
--   **Formalization Note.** Submodularity of $V_0$ is stated as supermodularity of $-V_0$ with the platform definition `SupermodularOn`, on the set $\{z : z_i \ge 0\ \forall i\}$.
-- source:
--   Karaesmen & van Ryzin, Overbooking with Substitutable Inventory Classes, Operations Research 52(1):83–104 (2004), p. 87, Lemma 1

import Mathlib
import Definitions.Def_SubstOverbooking_Structure_Setting
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

namespace SubstOverbooking.Structure

theorem lemma1_V0_submodular {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ) (c : Fin (m + 1) → ℝ)
    (hc : ∀ j, j ≠ 0 → 0 ≤ c j) :
    Supermodularity.Monotonicity.SupermodularOn (fun z => - V0 a c z) {z | ∀ i, 0 ≤ z i} := by sorry

end SubstOverbooking.Structure
