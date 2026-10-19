-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P05_oneBasisNotConcentrated
-- name    : QAlgorithms.Papers.Independent.Independent1.P05.oneBasisNotConcentrated
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:35:22.183187+00:00
-- url     : https://prove2.me/theorems/82de1fbf-8791-4b07-9928-26aa341d4611
-- title:
--   Lemma 2: one basis has no highly concentrated cluster
-- statement:
--   Consider a binary CSS presentation with $n,m_x,m_z>0$ and logical dimension $k\ge1$, satisfying Property 1 with $c_1,c_2,\delta_0>0$. Let $\rho$ be any density operator. Assume $\epsilon_1\ge0$, $2\epsilon_1<\delta_0$, $4c_1\epsilon_1<c_2$, and
--   $$
--   2c_1\epsilon_1\le\left(\frac{k-1}{4n}\right)^2.
--   $$
--   For the computed clusters in the preceding result, either every standard-basis cluster has $D_z$-mass strictly less than $99/100$, or every Hadamard-basis cluster has $D_x$-mass strictly less than $99/100$.
--
--   This uncertainty consequence selects a basis in which no single cluster captures almost all probability. It requires no low-energy hypothesis once the clusters are defined.
--
--   **Formalization Note** The subtraction $k-1$ takes place in the reals. The positive-$k$ reading comes from the section's positive-rate setting and is flagged for independent moderation.
--
--   **Correction to the printed source.**
--
--   Printed: The displayed finite lemma does not explicitly say k>=1, while Section 2 is introduced for constant-rate code families.
--
--   Corrected: State the finite lemma for k>=1 and n,mx,mz>0, keeping ((k-1)/(4n))^2 with real subtraction.
--
--   Reason: The proof uses a positive logical dimension; at k=0 the zero-radius clusters can concentrate in both bases. The finite positive-rate reading requires independent moderation.
-- source:
--   NLTS Hamiltonians from good quantum codes, arXiv:2206.13228v4, Lemma 2: one basis has no highly concentrated cluster, PDF p. 4. https://arxiv.org/abs/2206.13228v4 . PDF SHA-256: d7a1c5d8ee8ac147a6322005759342ac8154817d4e1534a9cc19b3da51b8875d.

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






























/-- Lemma 2, PDF p.4: positive logical dimension is the section's positive-rate regime.
The subtraction k-1 is real; the conclusion is a disjunction of universal statements. -/
theorem oneBasisNotConcentrated {n mx mz : ℕ} (C : CheckPresentation n mx mz)
    (hn : 0 < n) (hmx : 0 < mx) (hmz : 0 < mz) (hk : 1 ≤ C.logicalDimension)
    (c1 c2 delta0 eps1 : ℝ) (hcluster : NLTS.ClustersApproximateCodewords C c1 c2 delta0)
    (heps : 0 ≤ eps1) (hdomain : 2*eps1 < delta0) (hsmall : 4*c1*eps1 < c2)
    (hcutoff : 2*c1*eps1 ≤ (((C.logicalDimension : ℝ)-1)/(4*n))^2)
    (rho : Matrix (Qubits n) (Qubits n) ℂ) (hrho : IsDensityMatrix rho) :
    (∀ B ∈ nltsClasses C c1 eps1 false, nltsMass rho false B < 99/100) ∨
    (∀ B ∈ nltsClasses C c1 eps1 true, nltsMass rho true B < 99/100) := by sorry






end QAlgorithms.Papers.Independent.Independent1.P05
