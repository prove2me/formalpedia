-- Prove2me | Theorems.Thm_SubstOverbooking_Structure_semigroup_representation
-- name    : SubstOverbooking.Structure.semigroup_representation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:50.809804+00:00
-- url     : https://prove2.me/theorems/8fd22dbf-974e-4dd1-8bb6-c9554fb359c9
-- title:
--   Proof of Theorem 2, p. 88 — E[V₀(Z(u + εeᵢ))] = E[V₀(Z(u) + Y eᵢ)] with Y ~ Zᵢ(ε) independent
-- statement:
--   Assume every class has a semigroup family of survival laws on the parameter set $P$. Let $u \in P^n$, a class $i$ and $\varepsilon \in P$. Let $Z(u)$ have the product law of the survivals and let $Y$, independent of $Z(u)$, have the law of $Z_i(\varepsilon)$. Then
--
--   $$\mathbb E\big[V_0(Z(u + \varepsilon e_i), c)\big] = \mathbb E\big[V_0(Z(u) + Y e_i, c)\big],$$
--
--   where $e_i$ is the $i$-th unit vector.
--
--   This is the coupling step of the proof of Theorem 2: increasing one overbooking level by $\varepsilon$ is the same, in law, as adding an independent block of survivors to that class, which reduces the expected-value inequalities to sample-path inequalities for $V_0$.
-- source:
--   Karaesmen & van Ryzin, Overbooking with Substitutable Inventory Classes, Operations Research 52(1):83–104 (2004), p. 88, proof of Theorem 2, display after (8)

import Mathlib
import Definitions.Def_SubstOverbooking_Structure_Setting

namespace SubstOverbooking.Structure

open MeasureTheory

theorem semigroup_representation {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ) (c : Fin (m + 1) → ℝ)
    (P : Set ℝ) (L : Fin n → ℝ → PMF ℕ) (hL : ∀ i, IsSemigroupFamily P (L i))
    (u : Fin n → ℝ) (hu : ∀ k, u k ∈ P) (i : Fin n) (ε : ℝ) (hε : ε ∈ P) :
    ∫ z, V0 a c (fun k => (z k : ℝ)) ∂(survivalLaw L (Function.update u i (u i + ε))) =
      ∫ p : (Fin n → ℕ) × ℕ, V0 a c (fun k => ((p.1 + (Pi.single i p.2 : Fin n → ℕ)) k : ℝ))
        ∂((survivalLaw L u).prod (L i ε).toMeasure) := by sorry

end SubstOverbooking.Structure
