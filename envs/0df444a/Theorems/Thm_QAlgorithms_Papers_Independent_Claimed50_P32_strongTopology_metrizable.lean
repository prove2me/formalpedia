-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P32_strongTopology_metrizable
-- name    : QAlgorithms.Papers.Independent.Claimed50.P32.strongTopology_metrizable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:24:57.725995+00:00
-- url     : https://prove2.me/theorems/c2090075-1a6a-40dc-bc22-b739d31b7f5e
-- title:
--   Strong topology of quantum operations is metrizable
-- statement:
--   Let $\mathcal H$ and $\mathcal H^{\prime}$ be arbitrary nonzero separable complex Hilbert spaces. Let $\mathfrak F_{\leq 1}$ consist of all completely positive trace-nonincreasing complex-linear maps between their full trace-class spaces, with pointwise trace-norm convergence on all input states. Then
--
--   $$\mathfrak F_{\leq 1}(\mathcal H,\mathcal H^{\prime})\text{ is metrizable}.$$
--
--   This identifies a metric-compatible topology for approximation without imposing finite dimension or finite Kraus rank.
-- source:
--   On approximation of quantum channels, arXiv:0711.2245v1, PDF p. 6, §3, unnumbered: metrizability of the operation topology

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P32

noncomputable section

open Filter

open scoped Topology ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Claimed50.P32

open QAlgorithms.RealRegisters (Hilbert)

/-- §3, PDF p.6: metrizability of the specified pointwise trace-norm topology
on all quantum operations between arbitrary nonzero separable Hilbert spaces. -/
theorem strongTopology_metrizable {I J : Type}
    [Countable I] [Nonempty I] [Countable J] [Nonempty J] : TopologicalSpace.MetrizableSpace (CanonicalOperation I J) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P32

end
