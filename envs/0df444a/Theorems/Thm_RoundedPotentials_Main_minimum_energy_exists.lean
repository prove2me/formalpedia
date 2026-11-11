-- Prove2me | Theorems.Thm_RoundedPotentials_Main_minimum_energy_exists
-- name    : RoundedPotentials.Main.minimum_energy_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T08:35:02.145553+00:00
-- url     : https://prove2.me/theorems/bf7ffb36-70c8-4a97-b12d-38c4f0fe4f42
-- title:
--   §3.2, eq. (8) — existence of a minimum-energy flow
-- statement:
--   Let $b$ be any prescribed real excess vector for the finite integer-capacity network. If at least one capacity-feasible assignment realizes $b$, then there exists a capacity-feasible assignment $f^\star$ with the same excess such that
--   $$\Phi(f^\star)\le\Phi(g)\quad\text{for every capacity-feasible }g\text{ with }\operatorname{ex}_g=b.$$
--   The energy is $\Phi(f)=\sum_{c_{uv}>0}f_{uv}^2/(2c_{uv})$. This is an attained minimum, not an infimum value with an unspecified default. It includes the maximum-flow case used in §3.2 and the arbitrary feasible excess vectors used in Lemmas 3.4–3.5.
--
--   Differences from the source:
--   - encoding: a finite vertex set V of size n → vertices Fin n and an edge list with distinct loopless ordered pairs; reason: relabeling preserves every flow and cut; m is the actual list length; zero capacities are explicitly allowed in §3
--   - generalization: minimum-energy maximum flow of value p → a minimizer for any feasible prescribed excess vector b, including W=0 and empty or singleton vertex sets; reason: the same finite closed bounded feasible set and continuous energy argument applies; b=p(e_s−e_t) on the source network gives its full case; empty and singleton cases have only the zero assignment
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 13, §3.2, eq. (8) and the sentence after it

import Mathlib
import Definitions.Def_RoundedPotentials_Main_EnergyResidual

namespace RoundedPotentials.Main
open scoped BigOperators

theorem minimum_energy_exists {n W : ℕ} (I : Instance n W) (b : Fin n → ℝ)
    (hb : ∃ g : Assignment n, CapacityFeasible I g ∧ HasExcess g b) :
    ∃ f : Assignment n, MinimumEnergy I b f := by sorry

end RoundedPotentials.Main
