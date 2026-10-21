-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P32_specialCurve_ultrametric
-- name    : QAlgorithms.Papers.Independent.Renew46.P32.specialCurve_ultrametric
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:13:57.906073+00:00
-- url     : https://prove2.me/theorems/f0f72c62-89b9-4604-aca1-1230dc965264
-- title:
--   Special curve lemma over an ultrametric field
-- statement:
--   Let $K$ be a nontrivially valued ultrametric field, let $0\ne\rho\in K$ satisfy $|\rho|<1$, and let $E$ be a Hausdorff metrizable topological $K$-vector space. Let $U\subseteq E$ be open, $x\in U$, and let $(a_n),(b_n)$ in $U$ converge to $x$. There exist a strictly increasing injective map $m:\mathbb N_{>0}\to\mathbb N_{>0}$ and a smooth curve $c:K\to U$ such that
--   $$c(\rho^k)=\begin{cases}a_{m(k)}&k\text{ odd},\\b_{m(k)}&k\text{ even},\end{cases}\qquad c(0)=x.$$
--
--   Its restriction to $K^\times$ is locally constant; $|t|=|s|$ implies $c(t)=c(s)$; and $c(K^\times)=\{c(\rho^k):k\ge1\}$. These are all five source clauses. The field need not be complete.
-- source:
--   Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields, arXiv:math/0303300v1, PDF p. 52, Lemma 11.1 (Special Curve Lemma: Ultrametric Case)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

namespace QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

/-- Lemma 11.1, PDF p. 52: all five conclusions; interpolation indices
are positive integers and the field is not required to be complete. -/
theorem specialCurve_ultrametric
    {K : Type} [NontriviallyNormedField K] (hUltra : IsUltrametricField K)
    {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul K E] [T2Space E] [TopologicalSpace.MetrizableSpace E]
    (rho : K) (hRho0 : rho ≠ 0) (hRho1 : ‖rho‖ < 1)
    (U : Set E) (hU : IsOpen U) (x : U) (a b : ℕ+ → U)
    (ha : Tendsto (fun n => (a n : E)) atTop (𝓝 (x : E)))
    (hb : Tendsto (fun n => (b n : E)) atTop (𝓝 (x : E))) :
    ∃ m : ℕ+ → ℕ+, Function.Injective m ∧ StrictMono m ∧
    ∃ c : K → U, fieldSmooth (K := K) Set.univ (fun t => (c t : E)) ∧
      (∀ k : ℕ+, c (rho ^ (k : ℕ)) = if Odd (k : ℕ) then a (m k) else b (m k)) ∧
      c 0 = x ∧
      IsLocallyConstant (fun t : {t : K // t ≠ 0} => c t.val) ∧
      (∀ t s : K, ‖t‖ = ‖s‖ → c t = c s) ∧
      c '' {t : K | t ≠ 0} = {y | ∃ k : ℕ+, c (rho ^ (k : ℕ)) = y} := by sorry

end QAlgorithms.Papers.Independent.Renew46.P32
