-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P32_specialCurve_real
-- name    : QAlgorithms.Papers.Independent.Renew46.P32.specialCurve_real
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:14:19.703116+00:00
-- url     : https://prove2.me/theorems/1038dc3c-0811-4043-9622-65549feab864
-- title:
--   Special curve lemma over the real field
-- statement:
--   Let $E$ be a Hausdorff metrizable real topological vector space, $U\subseteq E$ open, $x\in U$, and $(a_n),(b_n)$ sequences in $U$ converging to $x$. For $0<\rho<1$, there are a strictly increasing injective $m:\mathbb N_{>0}\to\mathbb N_{>0}$ and a smooth $c:\mathbb R\to U$ interpolating $a_{m(k)}$ at odd powers $\rho^k$ and $b_{m(k)}$ at even powers. In addition $c(0)=x$, $c(t)=c(-t)$, $c$ is constant on $[\rho,\infty)$, and for every $k\ge1$,
--   $$c([\rho^{k+1},\rho^k])=\operatorname{conv}\{c(\rho^{k+1}),c(\rho^k)\}.$$
--
--   The image equality is exact, and the entire curve takes values in $U$, even when $U$ is not convex. No local convexity of $E$ is imposed.
-- source:
--   Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields, arXiv:math/0303300v1, PDF p. 54, Lemma 11.2 (Special Curve Lemma: Real Case)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

namespace QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

/-- Lemma 11.2, PDF pp. 54--55: exact segment images, evenness and the
constant outer ray, without local convexity of E. -/
theorem specialCurve_real
    {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [TopologicalSpace.MetrizableSpace E]
    (rho : ℝ) (hRho0 : 0 < rho) (hRho1 : rho < 1)
    (U : Set E) (hU : IsOpen U) (x : U) (a b : ℕ+ → U)
    (ha : Tendsto (fun n => (a n : E)) atTop (𝓝 (x : E)))
    (hb : Tendsto (fun n => (b n : E)) atTop (𝓝 (x : E))) :
    ∃ m : ℕ+ → ℕ+, Function.Injective m ∧ StrictMono m ∧
    ∃ c : ℝ → U, fieldSmooth (K := ℝ) Set.univ (fun t => (c t : E)) ∧
      (∀ k : ℕ+, c (rho ^ (k : ℕ)) = if Odd (k : ℕ) then a (m k) else b (m k)) ∧
      c 0 = x ∧ (∀ t : ℝ, c t = c (-t)) ∧
      (∀ k : ℕ+, (fun t => (c t : E)) '' Set.Icc (rho ^ ((k : ℕ) + 1)) (rho ^ (k : ℕ)) =
        segment ℝ (c (rho ^ ((k : ℕ) + 1)) : E) (c (rho ^ (k : ℕ)) : E)) ∧
      Set.EqOn c (fun _ => c rho) (Set.Ici rho) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P32
