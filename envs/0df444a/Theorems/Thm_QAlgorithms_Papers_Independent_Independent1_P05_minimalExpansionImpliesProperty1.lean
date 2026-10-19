-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P05_minimalExpansionImpliesProperty1
-- name    : QAlgorithms.Papers.Independent.Independent1.P05.minimalExpansionImpliesProperty1
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:35:51.403115+00:00
-- url     : https://prove2.me/theorems/83d2283e-6a7e-424d-9ca2-c90784670ef4
-- title:
--   Section 3: minimal-representative expansion implies Property 1
-- statement:
--   Let $F$ be a family of binary CSS check presentations. Fix positive $\alpha_x,\beta_x,\alpha_z,\beta_z,\bar\delta,a,b$ and $n_0\ge1$. For all $n\ge n_0$, suppose $an\le m_x(n),m_z(n)\le bn$. For every $0\le\delta<\bar\delta$, define $V_z^\delta$ as the words in $G_z^\delta$ of minimum Hamming weight within their coset modulo $C_X^\perp$, and define $V_x^\delta$ analogously modulo $C_Z^\perp$. Assume $H_X$ is $(\alpha_x,\beta_x)$-expanding on $V_x^\delta$ and $H_Z$ is $(\alpha_z,\beta_z)$-expanding on $V_z^\delta$. Then there are constants $c_1,c_2,\delta_0>0$, independent of $n$, such that for all $n\ge n_0$ and $0\le\delta<\delta_0$,
--   $$
--   y\in G_z^\delta\Longrightarrow
--   |y|_{C_X^\perp}\le c_1\delta n\ \text{or}\ |y|_{C_X^\perp}\ge c_2n,
--   $$
--   and the same dichotomy holds on the $X$ side modulo $C_Z^\perp$.
--
--   This derives Property 1 from uniform expansion of minimal representatives, without assuming the desired dichotomy. The check-density factors converting $\delta m_{\rm side}$ to a threshold relative to $n$ are retained.
-- source:
--   NLTS Hamiltonians from good quantum codes, arXiv:2206.13228v4, Section 3: minimal-representative expansion implies Property 1, PDF p. 6. https://arxiv.org/abs/2206.13228v4 . PDF SHA-256: d7a1c5d8ee8ac147a6322005759342ac8154817d4e1534a9cc19b3da51b8875d.

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



































/-- Section 3, PDF p.6: uniform expansion on constructed minimal-representative subsets
implies Property 1 uniformly in a family. Actual check-density factors are retained. -/
theorem minimalExpansionImpliesProperty1 (F : NLTSCheckFamily)
    (alphaX betaX alphaZ betaZ deltaBar lower upper : ℝ)
    (haX : 0 < alphaX) (hbX : 0 < betaX) (haZ : 0 < alphaZ) (hbZ : 0 < betaZ)
    (hd : 0 < deltaBar) (hl : 0 < lower) (hu : 0 < upper) (n0 : ℕ) (hn0 : 1 ≤ n0)
    (hrows : ∀ n ≥ n0,
      lower*n ≤ (F.rowsX n : ℝ) ∧ lower*n ≤ (F.rowsZ n : ℝ) ∧
      (F.rowsX n : ℝ) ≤ upper*n ∧ (F.rowsZ n : ℝ) ≤ upper*n)
    (hexp : ∀ n ≥ n0, ∀ delta : ℝ, 0 ≤ delta → delta < deltaBar →
      nltsExpanding (F.checks n).HX (nltsMinimal (F.checks n) true delta) alphaX betaX ∧
      nltsExpanding (F.checks n).HZ (nltsMinimal (F.checks n) false delta) alphaZ betaZ) :
    ∃ c1 c2 delta0 : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < delta0 ∧
      ∀ n ≥ n0, NLTS.ClustersApproximateCodewords (F.checks n) c1 c2 delta0 := by sorry

end QAlgorithms.Papers.Independent.Independent1.P05
