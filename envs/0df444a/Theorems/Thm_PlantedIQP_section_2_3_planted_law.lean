-- Prove2me | Theorems.Thm_PlantedIQP_section_2_3_planted_law
-- name    : PlantedIQP.section_2_3_planted_law
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:23:23.098919+00:00
-- url     : https://prove2.me/theorems/58aa31dc-6f73-459b-b625-1305c8b0ac08
-- title:
--   Section 2.3 — the planted law: uniform lower part independent of $(g^{(3)},V)$
-- statement:
--   Let $h\le n$ and let $(g,V)$ be drawn from the planted law ($g=\tilde f\circ A$, $V=A^{-1}U$). Then
--
--   1. the lower-degree part $g^{(2)}+g^{(1)}$ is uniformly random and independent of the pair $(g^{(3)},V)$: for every cubic form $g_3$, every lower-degree polynomial $r$ and every subspace $W$,
--   $$\Pr\big[g^{(3)}=g_3,\ g^{(2)}+g^{(1)}=r,\ V=W\big]=\Pr\big[g^{(3)}=g_3,\ V=W\big]\cdot\frac1{|\{\text{lower-degree polynomials}\}|};$$
--   2. $V$ is uniformly distributed over the $h$-dimensional subspaces of $\mathbb F_2^n$;
--   3. almost surely $\dim V=h$ and $T_g(u,v,w)=0$ for all $u,v,w\in V$;
--   4. consequently $P_3(n,h)$ is an instance of $M(n)$: there is a distribution $D$ on cubic polynomials with $P_3(n,h)=M(n)$ for that $D$.
--
--   Item 4 is what allows the moment bounds of Lemma 30 and the completeness of Lemma 35 to be applied to planted instances.
--
--   Differences from the source:
--   - generalization: 1 ≤ h ≤ n → h ≤ n; reason: h = 0 plants nothing and the statement still holds; it specializes to the source's range
--   - generalization: the paragraph's conclusions (uniform lower part independent of (g^{(3)}, V); V uniform; T_g|_{V³} = 0) → also item 4, P₃(n,h) = M(n) for some D; reason: item 4 follows from item 1 and is the form used in the proof of Theorem 43 (ii)
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Section 2.3, p.17

import Mathlib
import Definitions.Def_PlantedIQP_distributions
import Definitions.Def_PlantedIQP_triForm

set_option autoImplicit false

namespace PlantedIQP

/-- Bläser, Gullans, Hangleiter, Liu, Qiao, *Verifiable quantum advantage based on polynomials with
planted structures*, arXiv:2609.39918 (sha256 6e261694…), Section 2.3, p.17: under the planted law, with `g = f̃ ◦ A` and
`V = A⁻¹U`, `1 ≤ h ≤ n` (here `h ≤ n`): (a) the lower-degree part `g^{(2)} + g^{(1)}` is uniformly random and
independent of the pair `(g^{(3)}, V)`; (b) `V` is a uniformly random `h`-dimensional subspace;
(c) almost surely `dim V = h` and `T_g|_{V³} = 0`; consequently (d) `P₃(n, h)` is an instance of
`M(n)` for a suitable cubic-part law `D`. -/
theorem section_2_3_planted_law (n h : ℕ) (hh : h ≤ n) :
    (∀ (g3 r : CubicPoly n) (W : Submodule (ZMod 2) (Vec n)), r.c3 = 0 →
      plantedProb n h (fun g V => g.cubicPart = g3 ∧ g.lowerPart = r ∧ V = W) =
        plantedProb n h (fun g V => g.cubicPart = g3 ∧ V = W) /
          ((Finset.univ.filter fun g' : CubicPoly n => g'.c3 = 0).card : ℝ)) ∧
      (∀ W : Submodule (ZMod 2) (Vec n), Module.finrank (ZMod 2) W = h →
        plantedProb n h (fun _ V => V = W) =
          1 / (Nat.card {W' : Submodule (ZMod 2) (Vec n) // Module.finrank (ZMod 2) W' = h} : ℝ)) ∧
      plantedProb n h (fun g V => Module.finrank (ZMod 2) V = h ∧
        ∀ u ∈ V, ∀ v ∈ V, ∀ w ∈ V, triForm g u v w = 0) = 1 ∧
      ∃ D : PMF (CubicPoly n), ∀ g : CubicPoly n, plantedWeight n h g = mixM D g := by sorry

end PlantedIQP
