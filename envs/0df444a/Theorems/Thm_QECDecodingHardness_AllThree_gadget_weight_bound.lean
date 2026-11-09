-- Prove2me | Theorems.Thm_QECDecodingHardness_AllThree_gadget_weight_bound
-- name    : QECDecodingHardness.AllThree.gadget_weight_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:35.383649+00:00
-- url     : https://prove2.me/theorems/b08294b6-cc1b-4f3c-9727-6a312865f83f
-- title:
--   Lemma 3 — total weight bound and equality case
-- statement:
--   Partition a syndrome σ into a finite family of gadgets g satisfying Assumption 2. Write R_g for their disjoint neighborhoods, m_g for their integer error excesses from Eq. (1), m=∑_g m_g, and |σ| for the number of defects, counting a combined Y defect once. If E is any allowed error with syndrome σ, then
--
--   $$|E|\ge |\sigma|+m.$$
--
--   If equality holds, the connected cover of every gadget is a minimal cover: it attains that gadget's local covering minimum and is supported in R=⋃_g R_g. The connected cover is computed from E's actual supported components, with its Pauli values retained.
--
--   This is the global weight certificate and the full equality consequence used by the paper. It assumes only the abstract gadget setup and separation; concrete construction properties are obligations of the hardness proof, not hypotheses of the goal.
--
--   Differences from the source:
--   - generalization: gadgets in the three finite decoding settings → gadgets in any finite local binary check system with disjoint nonempty defect blocks; reason: the counting arguments use only local syndrome incidence, support weight and the stated neighborhoods; the three physical models specialize this interface
--   - encoding: a gadget defect is a constraint, with adjacent X and Z constraints combined as a Y defect → disjoint nonempty constituent-check blocks, with radius three Tanner reach for combined Y defects and radius one otherwise; reason: keeps the source defect count, cover condition and special 2-neighborhood while making the underlying binary checks explicit
--   - encoding: the attained covering minimum in Eq. (1) and the integer excess m_g → Nat.find with an explicit cover witness, followed by subtraction in ℤ; reason: cover existence is implicit in Eq. (1); this represents the same minimum without an empty-set default or truncating negative excess
-- source:
--   Shouzhen (Bailey) Gu, Lily Wang, Aleksander Kubica, STOC 2027 submission #745 (October 2026), p.7, Lemma 3, with Eq. (1) and Assumption 2

import Definitions.Def_QECDecodingHardness_AllThree_gadgets

namespace QECDecodingHardness.AllThree

/-- Gu–Wang–Kubica, STOC 2027 submission #745 (October 2026), p.7, Lemma 3.
The full inequality and equality consequence, using the computed connected cover.
Cardinalities and all excesses are compared in ℤ. The abstract incidence formulation
also covers other finite local binary systems, without assuming their hardness. -/
theorem gadget_weight_bound (S : CheckSystem) (D : DefectPresentation S)
    (F : GadgetFamily D) (hsep : SeparatedGadgets F)
    (e : Error S) (he : Allowed S e) (hs : syndrome S e = gadgetSyndrome F) :
    (allDefects F).card + totalExcess F ≤ (errorWeight e : ℤ) ∧
    ((errorWeight e : ℤ) = (allDefects F).card + totalExcess F →
      ∀ i : Fin F.count, MinimalCover F i (connectedCover D (F.gadget i) e)) := by sorry

end QECDecodingHardness.AllThree
