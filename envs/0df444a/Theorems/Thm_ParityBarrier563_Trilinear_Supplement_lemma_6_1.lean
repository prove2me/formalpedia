-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_Supplement_lemma_6_1
-- name    : ParityBarrier563.Trilinear.Supplement.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:44:52.909594+00:00
-- url     : https://prove2.me/theorems/c7fcb12e-92d1-41b5-a9e9-846c26c54f32
-- title:
--   Lemma 6.1 — Decision trees with CNF/DNF leaves have bounded CNF norm
-- statement:
--   Let V be any finite variable set, $k\ge1$ and $R\ge0$ integers. Suppose F is computed by a binary decision tree of depth at most R with a k-CNF or k-DNF at each leaf, evaluated on the input reaching that leaf. Then
--   $$\operatorname{size}_k(F)\le2^{R+1}.$$
--   Leaf types may be mixed and R=0 is included. A leaf need agree with F only on its path subcube. This controls the CNF norm of partial decision trees.
--
--   Differences from the source:
--   - encoding: decision tree with leaf functions on path subcubes → an inductive finite LeafTree with eval equal to F; reason: the reached leaf alone determines the output, preserving all path-subcube instances
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), Lemma 6.1, printed p.26 / PDF p.28

import Definitions.Def_ParityBarrier563_Trilinear_Supplement_DecisionTree
import Definitions.Def_ParityBarrier563_Trilinear_Correlation

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- Lemma 6.1: R=0 and mixed CNF/DNF leaves are allowed. -/
theorem lemma_6_1 (V : Type) [Fintype V] [DecidableEq V]
    (k R : ℕ) (hk : 1 ≤ k) (F : BoolFn V) (T : LeafTree V)
    (hdepth : T.depth ≤ R) (hleaves : T.GoodLeaves k) (hF : T.eval = F) :
  sizeB k (ind F) ≤ (2 : ℝ)^(R+1) := by sorry

end ParityBarrier563.Trilinear.Supplement
