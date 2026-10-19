-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P05_separatedPositiveMassUnions
-- name    : QAlgorithms.Papers.Independent.Independent1.P05.separatedPositiveMassUnions
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:36:35.629375+00:00
-- url     : https://prove2.me/theorems/48ae55e9-b76d-4e82-b08a-cc1d877c5bd6
-- title:
--   Section 2: positive-mass separated unions
-- statement:
--   Let a binary CSS presentation on $n>0$ qubits satisfy Property 1 with $c_1,c_2,\delta_0>0$, and assume $\epsilon_1\ge0$, $2\epsilon_1<\delta_0$, and $4c_1\epsilon_1<c_2$. Fix either basis and any density operator $\rho$. Suppose its measurement distribution $D$ gives the approximate-code set mass at least $199/200$, while each computed class has mass less than $99/100$. Then there are disjoint subcollections $M,M'$ of the computed classes whose unions $S,S'$ are disjoint and satisfy
--   $$
--   D(S)\ge\frac1{400},\qquad D(S')\ge\frac1{400},
--   \qquad |x-y|\ge c_2n\quad(x\in S,\ y\in S').
--   $$
--
--   This extracts two positive-mass separated sets in whichever basis Lemma 2 selects. Both probability constants and the cross-union separation are retained.
-- source:
--   NLTS Hamiltonians from good quantum codes, arXiv:2206.13228v4, Section 2: positive-mass separated unions, PDF p. 5. https://arxiv.org/abs/2206.13228v4 . PDF SHA-256: d7a1c5d8ee8ac147a6322005759342ac8154817d4e1534a9cc19b3da51b8875d.

import Definitions.Def_QAlgorithms_Defs_NLTSPreparationCircuits
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P05_Model
set_option autoImplicit false

/-! Statements from Anshu--Breuckmann--Nirkhe, arXiv:2206.13228v4.
Theorem 5 and three construction-specific expansion claims are deferred in HARD.md.
All new definitions are specific to this paper. -/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P05

open PresentedCSS
































/-- Section 2 and footnote 1, PDF pp.4--5: positive-mass separated unions of computed
classes, in whichever basis has no cluster of mass at least 99/100. -/
theorem separatedPositiveMassUnions {n mx mz : ℕ} (C : CheckPresentation n mx mz)
    (hn : 0 < n) (c1 c2 delta0 eps1 : ℝ)
    (hcluster : NLTS.ClustersApproximateCodewords C c1 c2 delta0)
    (heps : 0 ≤ eps1) (hdomain : 2*eps1 < delta0) (hsmall : 4*c1*eps1 < c2)
    (rho : Matrix (Qubits n) (Qubits n) ℂ) (hrho : IsDensityMatrix rho) (had : Bool)
    (htotal : nltsMass rho had (nltsApprox C had eps1) ≥ 199/200)
    (heach : ∀ B ∈ nltsClasses C c1 eps1 had, nltsMass rho had B < 99/100) :
    ∃ M M2 : Finset (Finset (NLTSWord n)), M ⊆ nltsClasses C c1 eps1 had ∧
      M2 ⊆ nltsClasses C c1 eps1 had ∧ Disjoint M M2 ∧
      Disjoint (nltsClusterUnion M) (nltsClusterUnion M2) ∧
      nltsMass rho had (nltsClusterUnion M) ≥ 1/400 ∧
      nltsMass rho had (nltsClusterUnion M2) ≥ 1/400 ∧
      ∀ x ∈ nltsClusterUnion M, ∀ y ∈ nltsClusterUnion M2,
        c2*n ≤ (hammingDist x y : ℝ) := by sorry




end QAlgorithms.Papers.Independent.Independent1.P05
