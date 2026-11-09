-- Prove2me | Theorems.Thm_SharpPauliEntanglement_Exact_negativity_above_tree_threshold
-- name    : SharpPauliEntanglement.Exact.negativity_above_tree_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:58:45.921642+00:00
-- url     : https://prove2.me/theorems/d0d5c50d-58fe-4309-bfd6-e65f8529901e
-- title:
--   Lemma 4.2 — For every s∈(tΔ,1), some finite complete rooted (Δ−1)-ary tree has qT(s)<0
-- statement:
--   For an integer $\Delta\ge2$, set $b=\Delta-1$ and use the exact $t_\Delta$ of (1.4). For every real $s$ satisfying $t_\Delta<s<1$, there exists a finite height $h$ such that the complete rooted $b$-ary tree $T_h$ satisfies
--
--   $$q_{T_h}(s)=\sum_{U\subseteq V(T_h)}(-1)^{|\mathcal C(T_h[U])|}s^{|U|}<0.$$
--
--   This is strict negativity on a finite tree at the chosen value of $s$, rather than a limiting claim. Together with the partial-transpose eigenvalue in (4.3), it establishes entanglement above the threshold.
--
--   Differences from the source:
--   - encoding: a finite complete rooted b-ary tree → all words over Fin b of length at most an existential finite height h, with extension edges; reason: this is the source complete rooted tree at each height, including b = 1
-- source:
--   Bobak T. Kiani, Sharp universal death of entanglement threshold for Pauli Hamiltonians, STOC 2027 submission #159 (October 2026), printed/PDF p. 19, Lemma 4.2

import Definitions.Def_SharpPauliEntanglement_Exact_TreeHamiltonian

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
namespace SharpPauliEntanglement.Exact

/-- Kiani, p. 19, Lemma 4.2: a finite complete rooted (Δ-1)-ary tree, not a limit. -/
theorem negativity_above_tree_threshold (Δ : ℕ) (hΔ : 2 ≤ Δ)
    (s : ℝ) (hs : criticalT Δ < s) (hs1 : s < 1) :
    ∃ h : ℕ, componentPolynomial (completeTreeGraph (Δ - 1))
      (completeTreeVertices (Δ - 1) h) s < 0 := by sorry

end SharpPauliEntanglement.Exact
