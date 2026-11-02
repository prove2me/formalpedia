-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P59_based_twisted_loops_identity_component
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P59.based_twisted_loops_identity_component
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:26:43.777207+00:00
-- url     : https://prove2.me/theorems/15858db6-7011-499f-a47b-ebe3c5c86d26
-- title:
--   Based twisted loops take values in the identity path component
-- statement:
--   Let $G$ be a compactly generated topological group, let $\alpha\in G$, and let $G^0$ denote the path component of its identity. Define
--
--   $$
--   \Omega_{(\alpha)}G=\{\gamma\in C(\mathbb R,G):\gamma(t+1)=\alpha\gamma(t)\alpha^{-1}\text{ for every }t\in\mathbb R,\ \gamma(0)=1\}.
--   $$
--
--   Every such loop takes values in $G^0$. Restricting its codomain gives the canonical identification
--
--   $$
--   \Omega_{(\alpha)}G\cong\Omega_{\operatorname{Ad}(\alpha)|_{G^0}}G^0.
--   $$
--
--   This is an identification of topological groups, with compactly generated compact-open topologies and pointwise operations. If $G$ is discrete, $\Omega_{(\alpha)}G$ consists solely of the constant identity loop. The twist $\alpha$ is arbitrary and need not lie in $G^0$.
--
--   **Formalization Note** Lean states equality of the sets after inclusion in $C(\mathbb R,G)$, together with a homeomorphism that preserves every evaluation. Evaluation preservation also preserves the pointwise group operations. No connected component is substituted for the path component.
-- source:
--   Mapping stacks of topological stacks, arXiv:0809.2373v2, PDF p. 14, Unnumbered §7: based twisted loops see only G0

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P59

namespace QAlgorithms.Papers.Independent.Intakethird100.P59

universe u v

/-- Unnumbered identity-component assertion, PDF p.14. The equality is via
inclusion of G0 into G, with Ad(alpha) restricted to G0. Both groups are the
same set of continuous G-valued functions, hence have the same induced
compact-open (and compactly generated compact-open) topology and pointwise
operations. The discrete specialization asserts the entire group is trivial. -/
theorem based_twisted_loops_identity_component
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactlyGeneratedSpace G] (alpha : G) :
    basedTwistedLoopSet alpha =
      includeIdentityLoop '' identityBasedTwistedLoopSet alpha ∧
    (∃ e : KSubspace C(ℝ, G) (basedTwistedLoopSet alpha) ≃ₜ
        KSubspace C(ℝ, pathComponent (1 : G)) (identityBasedTwistedLoopSet alpha),
      ∀ gamma t, ((e gamma).1 t).1 = gamma.1 t) ∧
    (DiscreteTopology G → basedTwistedLoopSet alpha = {1}) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P59
