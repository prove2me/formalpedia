-- Prove2me | Theorems.Thm_QECDecodingHardness_AllThree_isolated_defects_nonnegative_excess
-- name    : QECDecodingHardness.AllThree.isolated_defects_nonnegative_excess
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:41.203204+00:00
-- url     : https://prove2.me/theorems/b41f0395-1268-4adc-9df9-42aa686529f0
-- title:
--   Lemma 6 — isolated defects have nonnegative error excess
-- statement:
--   Let g be a gadget, R_g its neighborhood, and m_g its integer error excess, defined by the least local covering weight minus the number of defects in g. Suppose distinct defects of g are at Tanner distance at least four from one another. Then
--
--   $$m_g\ge0.$$
--
--   The Tanner metric is the bipartite check–error-location metric. Disconnected defects satisfy the separation condition, and distance four is included. For combined defect blocks the condition is imposed between every constituent check of distinct blocks.
--
--   This local lower bound applies to isolated-defect gadgets; it does not say that arbitrary surface-code gadgets have nonnegative excess. The same covers, neighborhoods and signed excess are used in Lemma 3.
--
--   Differences from the source:
--   - generalization: gadgets in the three finite decoding settings → gadgets in any finite local binary check system with disjoint nonempty defect blocks; reason: the counting arguments use only local syndrome incidence, support weight and the stated neighborhoods; the three physical models specialize this interface
--   - encoding: a gadget defect is a constraint, with adjacent X and Z constraints combined as a Y defect → disjoint nonempty constituent-check blocks, with radius three Tanner reach for combined Y defects and radius one otherwise; reason: keeps the source defect count, cover condition and special 2-neighborhood while making the underlying binary checks explicit
--   - encoding: the attained covering minimum in Eq. (1) and the integer excess m_g → Nat.find with an explicit cover witness, followed by subtraction in ℤ; reason: cover existence is implicit in Eq. (1); this represents the same minimum without an empty-set default or truncating negative excess
--   - encoding: Tanner distance at least four → every Tanner walk between distinct defects has length at least four; reason: agrees with graph distance, including disconnected pairs, without giving unreachable vertices a default distance zero
-- source:
--   Shouzhen (Bailey) Gu, Lily Wang, Aleksander Kubica, STOC 2027 submission #745 (October 2026), p.10, Lemma 6

import Definitions.Def_QECDecodingHardness_AllThree_gadgets

namespace QECDecodingHardness.AllThree

/-- Gu–Wang–Kubica, STOC 2027 submission #745 (October 2026), p.10, Lemma 6.
The exact threshold is four in the Tanner graph. The same definitions of local
weight, cover, neighborhood and signed excess are used as in Lemma 3. -/
theorem isolated_defects_nonnegative_excess (S : CheckSystem)
    (D : DefectPresentation S) (g : Gadget D) (hisolated : IsolatedDefects D g) :
    0 ≤ errorExcess D g := by sorry

end QECDecodingHardness.AllThree
