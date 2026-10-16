-- Prove2me | Theorems.Thm_StrategicAlloc_EFXFour_bundle_reduction
-- name    : StrategicAlloc.EFXFour.bundle_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T14:15:00.54982+00:00
-- url     : https://prove2.me/theorems/e5ef6662-f648-4515-a6d8-f6069f15880c
-- title:
--   §4.2, p. 19, proof of Theorem 4.5 — an EFX bundle below µ_1 is a singleton or one of {h_2, h_3}, {h_2, h_4}, {h_3, h_4}
-- statement:
--   Consider two agents and four goods with additive non-negative valuations, and name the goods $h_1, \dots, h_4$ so that
--   $$
--   v_1(h_1) \ge v_1(h_2) \ge v_1(h_3) \ge v_1(h_4) > 0.
--   $$
--   Let $(A_1, A_2)$ be an EFX allocation in which agent 1 receives strictly less than her maximin share, $v_1(A_1) < \mu_1$. Then agent 1's bundle is a singleton or one of three pairs:
--   $$
--   |A_1| = 1 \quad\text{or}\quad A_1 \in \bigl\{\{h_2, h_3\},\ \{h_2, h_4\},\ \{h_3, h_4\}\bigr\}.
--   $$
--
--   This is the case split of the proof of Theorem 4.5: each of the four possibilities is then ruled out separately, three of them with the equilibrium property.
--
--   **Formalization Note** The renaming is a bijection $h$ of `Fin 4` with $h_j$ = `h (j - 1)`, so $\{h_2, h_3\}$ is `{h 1, h 2}`. The EFX hypothesis is part of the page's context ("a PNE that produces an EFX allocation"); it is what excludes $A_1 = \emptyset$. The equilibrium is not used in this step and does not appear.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 19, proof of Theorem 4.5, sentence after Lemma 4.6

import Mathlib
import Definitions.Def_StrategicAlloc_EFXFour_Setting

namespace StrategicAlloc.EFXFour

theorem bundle_reduction (v : Fin 2 → Fin 4 → ℝ) (hv : ∀ i g, 0 ≤ v i g) (h : Fin 4 ≃ Fin 4)
    (h01 : v 0 (h 1) ≤ v 0 (h 0)) (h12 : v 0 (h 2) ≤ v 0 (h 1)) (h23 : v 0 (h 3) ≤ v 0 (h 2))
    (h3pos : 0 < v 0 (h 3))
    (A : Fin 2 → Finset (Fin 4)) (hA : StrategicAlloc.RRFair.IsAllocation A) (hEFX : StrategicAlloc.CutChoose.IsEFX v A)
    (hlt : StrategicAlloc.RRFair.val v 0 (A 0) < mu v 0) :
    (A 0).card = 1 ∨ A 0 = {h 1, h 2} ∨ A 0 = {h 1, h 3} ∨ A 0 = {h 2, h 3} := by sorry

end StrategicAlloc.EFXFour
