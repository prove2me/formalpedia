-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_relative_entropy_formula
-- name    : QAlgorithms.Papers.Independent.Independent1.P04.relative_entropy_formula
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:23:48.494458+00:00
-- url     : https://prove2.me/theorems/de78c258-f48b-4564-9542-0f4fd2120eef
-- title:
--   Relative-entropy coherence and its diagonal minimizer
-- statement:
--   Let $\rho$ be a density matrix of dimension $d\ge1$, and let $\Delta\rho$ delete its off-diagonal entries. Use natural-log entropy $S(\rho)=(\log2)S_2(\rho)$. The matrix $\Delta\rho$ is an incoherent density matrix, and
--   $$0\le C_{\rm rel}(\rho)=S(\Delta\rho)-S(\rho)=\min_{\delta\ {\rm diagonal}}D(\rho\|\delta)=D(\rho\|\Delta\rho).$$
--   Here $D$ is Umegaki relative entropy, infinite when the support condition fails, with $0\log0=0$. The statement includes singular states and proves the diagonal minimizer's optimality.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3, Eqs.(1), (5), (8), PDF p. 3. https://arxiv.org/abs/1311.0275v3 . PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825.

import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
set_option autoImplicit false

/-! Quantifying Coherence, arXiv:1311.0275v3. Fixed bases and arbitrary finite dimensions.
Local predicates apply to density matrices only; invalid matrices carry no coherence guarantees. -/

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P04

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq























































/-- PDF pp.1,3, (1), (5), (8): the diagonal minimizer, including singular states; natural logs. -/
theorem relative_entropy_formula (d : ℕ) (hd : 0 < d) (rho : CoherenceMatrix d)
    (hrho : IsDensityMatrix rho) :
    0 ≤ entropyCoherence d rho ∧
    ∃ hdiag : IsDensityMatrix (dephasedMatrix rho),
      IncoherentState (dephasedMatrix rho) ∧
      QuantumLoss.umegakiEntropy rho (dephasedMatrix rho) hrho hdiag =
        ENNReal.ofReal (entropyCoherence d rho) ∧
      ∀ delta, ∀ hdelta : IsDensityMatrix delta, BasisDiagonal delta →
        ENNReal.ofReal (entropyCoherence d rho) ≤
          QuantumLoss.umegakiEntropy rho delta hrho hdelta := by sorry











end QAlgorithms.Papers.Independent.Independent1.P04
