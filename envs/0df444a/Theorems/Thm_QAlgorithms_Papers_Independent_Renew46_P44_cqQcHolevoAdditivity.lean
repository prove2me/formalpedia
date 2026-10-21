-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_cqQcHolevoAdditivity
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.cqQcHolevoAdditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:25:26.382087+00:00
-- url     : https://prove2.me/theorems/af2ea793-c5f4-4b90-823a-a1f9c831079b
-- title:
--   Proposition 1: Holevo additivity for c-q and q-c channels
-- statement:
--   Let $\Phi$ be a completely positive trace-preserving channel on a nonzero complex Hilbert space. Assume either the c-q form $\Phi[S]=\sum_i S_i\langle e_i,S e_i\rangle$ for a complete orthonormal basis $(e_i)$ and fixed densities $S_i$, or the q-c form $\Phi[S]=\sum_i\operatorname{Tr}(SX_i)|e_i\rangle\langle e_i|$ for a bounded positive weak resolution of the identity $(X_i)$. Then, for all positive integers $n,m$,
--
--   $$\bar C_n(\Phi)+\bar C_m(\Phi)=\bar C_{n+m}(\Phi).$$
--
--   Here $\bar C_n$ optimizes Holevo information over all discrete ensembles of block densities, including entangled inputs in the q-c case. This is the source's two channel classes, with no enlargement to all measure-and-prepare maps.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 6, Proposition 1: Holevo additivity for c-q and q-c channels

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P44

open Filter MeasureTheory

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tracePair)

open QAlgorithms.Papers.Independent.Frontier30.P14 (traceClassTensorPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 1, PDF pp.6-7. Two separate source channel classes; block
ensembles in holevoBlock include entangled inputs also in the q-c case. -/
theorem cqQcHolevoAdditivity {I : Type} [Nonempty I]
    (Phi : Matrix I I ℂ → Matrix I I ℂ) (hPhi : TC.IsTraceClassChannel Phi)
    (hclass : IsCq Phi ∨ IsQc Phi) (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    holevoBlock Phi n + holevoBlock Phi m = holevoBlock Phi (n + m) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
