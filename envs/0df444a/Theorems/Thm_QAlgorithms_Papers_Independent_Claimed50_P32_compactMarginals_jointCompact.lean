-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P32_compactMarginals_jointCompact
-- name    : QAlgorithms.Papers.Independent.Claimed50.P32.compactMarginals_jointCompact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:30:17.90322+00:00
-- url     : https://prove2.me/theorems/c5072780-32d8-4a99-ad21-c21bfef08d10
-- title:
--   Compact marginal constraints give a compact joint operator set
-- statement:
--   Let $A\subseteq\mathfrak T_1(\mathcal H)$ and $B\subseteq\mathfrak T_1(\mathcal K)$ be trace-norm compact, where $\mathfrak T_1$ denotes positive trace-class operators of trace at most one and both Hilbert spaces are nonzero and separable. Then
--
--   $$\{C\in\mathfrak T_1(\mathcal H\otimes\mathcal K):\operatorname{Tr}_{\mathcal K}C\in A,\ \operatorname{Tr}_{\mathcal H}C\in B\}\text{ is trace-norm compact}.$$
--
--   Empty and trace-incompatible constraints are permitted. This is the valid sufficient direction explicitly proved in the Appendix; the printed converse is deferred separately.
-- source:
--   On approximation of quantum channels, arXiv:0711.2245v1, PDF p. 24, §6, proof of Corollary: valid compact-marginals implication

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P32

noncomputable section

open Filter

open scoped Topology ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Claimed50.P32

open QAlgorithms.RealRegisters (Hilbert)

/-- §6, Appendix Corollary proof, PDF p.24: compact marginal constraint sets
imply compactness of the joint set. The false printed reverse direction is
explicitly deferred; empty and trace-incompatible constraints are permitted. -/
theorem compactMarginals_jointCompact {I J : Type}
    [Countable I] [Nonempty I] [Countable J] [Nonempty J] (A : Set (TraceSubstate I)) (B : Set (TraceSubstate J))
    (hA : IsCompact A) (hB : IsCompact B) :
    IsCompact (jointMarginalSet A B) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P32

end
