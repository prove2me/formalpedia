-- Prove2me | Theorems.Thm_ShortestPlanarDisjoint_Main_lemma_5_2
-- name    : ShortestPlanarDisjoint.Main.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:56.605706+00:00
-- url     : https://prove2.me/theorems/f9bc7d40-542b-406b-b25c-bb8e226675f7
-- title:
--   Lemma 5.2 — Stack encoding
-- statement:
--   Fix a disk layout, a crossing budget $b\ge1$, and all return-free noncrossing
--   perfect matchings of its terminal and seam-side endpoints. On each seam side,
--   every closing endpoint precedes every opening endpoint. Moreover, the seam counts,
--   side-opening counts and terminal opening/closing bits determine the state uniquely:
--
--   $$\operatorname{code}(D)=\operatorname{code}(E)\quad\Longrightarrow\quad D=E.$$
--
--   The result concerns every state within the budget, including states not realized
--   by a graph. It supplies the finite state encoding used by the signature argument.
--
--   Differences from the source:
--   - generalization: the planar side order (1), with r=f−1 and nonempty used-face terminal blocks → any fixed disk-side order and any number of seams, allowing empty terminal blocks and an empty endpoint set; reason: the assertion uses only disk noncrossing and no-return conditions, which also apply to empty blocks and endpoint sets; every source planar layout is one allowed layout
--   - encoding: a noncrossing matching of ordered endpoints and its stack code → an involutive permutation with no fixed points, and a concatenated list of counts and bits; reason: each unordered pair and each code component is represented exactly once; equality includes counts and matching but no geometric shape
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Lemma 5.2, p. 16 (PDF p. 18)

import Definitions.Def_ShortestPlanarDisjoint_Main_DiskState

set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main

/-- The disk assertion is independent of the genus and of the side gluing.
It therefore applies to the planar boundary order (1) and the surface cuts. -/
theorem lemma_5_2 {k f r b : ℕ} (L : DiskLayout k f r) (hb : 1 ≤ b) :
    (∀ D : DiskState L b, D.ClosingsBeforeOpenings) ∧
      Function.Injective (fun D : DiskState L b => D.stackCode) := by sorry

end ShortestPlanarDisjoint.Main
