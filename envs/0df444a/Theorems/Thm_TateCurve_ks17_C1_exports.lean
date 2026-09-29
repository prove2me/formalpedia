-- Prove2me | Theorems.Thm_TateCurve_ks17_C1_exports
-- name    : TateCurve.ks17_C1_exports
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/75caa134-8d3f-5500-8fba-90f3a99519b2
-- title:
--   Envelope-engine interface lemmas for the Tate addition law
-- statement:
--   Over a nontrivially normed, ultrametric, complete field $K$, the theorem is a conjunction of seven statements. (1) Given $q,u,v\in K$, a bound $B\ge 0$, an exponent $d$, index sets $s:\mathbb N\to\mathbb N\to\mathrm{Finset}\,\mathbb Z$ and coefficients $a$ with $\lVert a_{M,k,j}\rVert\le B(M+1)^d$, if for every $q',u',v'$ satisfying `ExpansionRegion` (the conditions `AddParams`, $\lVert q'\rVert<1$ and the annulus bounds $\lVert q'\rVert<\lVert w\rVert$, $\lVert q'\rVert\lVert w\rVert<1$ for $w=u',v',u'v',u'v'^{-1}$) the series $\sum_M\bigl(\sum_{k=1}^M(\sum_{j\in s_{M,k}}a_{M,k,j}v'^j)(u'^k-u'^{-k})\bigr)q'^M$ sums to `addDefectDiff` $q'\,u'\,v'$, then for $q,u,v$ in the expansion region $(X(uv)-X(uv^{-1}))(X(u)-X(v))^2=-(2Y(u)+X(u))(2Y(v)+X(v))$ for the Tate point series $X=$ `pointX`, $Y=$ `pointY`, i.e. the defect vanishes. (2) For $w\ne 0$ and $d\in\mathbb N$, $(w-w^{-1})\sum_{j<d/2}\mathrm{tent}(w,d-1-2j)=\sum_{i=1}^{d-1}(d-i)(w^i-w^{-i})$, with $\mathrm{tent}(w,m)=w(\sum_{i<m}w^i)^2w^{-m}$ and natural-number subtraction in the indices. (3) $\mathrm{xCoeff}(w,n)=\sum_{f\mid n}f\,(w^f+w^{-f}-2)$. (4) For $u,v\ne 0,1$ with $uv\ne1$, $uv^{-1}\ne1$, $K$ of characteristic zero and $M>0$, `svComplex` $u\,v\,M$ equals an explicit five-block expression: two divisor sums over $M$ of products of $\mathrm{tent}$-telescopes in $u$ and $v$, a divisor sum pairing $G_z(u,d),G_z(v,d)$ with weighted telescopes $\sum_{i=1}^{d-1}(d-i)(\cdot)$, and two convolutions over $a\in[1,M)$ of $\sum_{d\mid a}d\,G_z(u,d)G_z(v,d)$ against $\mathrm{tent}$- and $\mathrm{xCoeff}$-sums. (5) For $d\in\mathbb N$ and $0<r<1$, $k\mapsto(k+1)^dr^k$ is summable. (6) For $q\ne0$ with $\lVert q\rVert<1$ and $a$ bounded as above, if the master relation $\sum_{k=1}^M R_{M,k}(w^k+w^{-k}-2)=\mathrm{specAlpha}+\mathrm{specTail}+\mathrm{specGamma}$ holds for the rows $R$ evaluated at all spectators $1+q^{n+1}$ and all $\lVert w\rVert>1$, then $\sum_{j\in s_{M,k}}a_{M,k,j}v^j=0$ for all $1\le k\le M$ and all $v\ne0$. (7) For $c$ with $\lVert c_{N,k}\rVert\le B(N+1)^d$ and $g$ invariant under $w\mapsto qw$ on the relevant region and representing $\sum_M(\sum_{k=1}^Mc_{M,k}(w^k+w^{-k}-2))q^M$ there, that same master relation $\sum_{k=1}^Mc_{M,k}(w^k+w^{-k}-2)=\mathrm{specAlpha}(c,w,M)+\mathrm{specTail}(c,w,M)+\mathrm{specGamma}(c,M)$ holds for all $M$ and all $\lVert w\rVert>1$.
--
--   These seven statements form the interface of the envelope-engine layer in the analytic verification that the Tate parametrisation $w\mapsto(X(w),Y(w))$ satisfies the symmetric addition identities of the curve $y^2+xy=x^3+a_4(q)x+a_6(q)$: the envelope argument that forces a $q$-expansion with polynomially bounded coefficients to vanish row by row, the $G_z$/tent telescopes, the divisor-sum form of the $x$-expansion coefficients, and the row-block normal form of the single-variable complex. They are consumed by [`TateCurve.diffHyp_unconditional`](thm.html#TateCurve.diffHyp_unconditional) and [`TateCurve.symAdd_sum_regional`](thm.html#TateCurve.symAdd_sum_regional).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_ks17_C1_exports.lean

import Mathlib
import Definitions.Def_TateCurve_XMultIdentities
import Definitions.Def_TateCurve_KeystoneVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open TateCurve FLT.DivisorConvolution FLT.DivisorConvolution.BesgeCertificate Finset

theorem TateCurve.ks17_C1_exports.{u_1} :

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u v : K} {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hexp : ∀ q' u' v' : K, ExpansionRegion q' u' v' →
      HasSum (fun M : ℕ =>
        (∑ k ∈ Finset.Icc 1 M,
            (∑ j ∈ s M k, a M k j * v' ^ j) * (u' ^ k - u'⁻¹ ^ k)) * q' ^ M)
        (addDefectDiff q' u' v'))
    (hreg : ExpansionRegion q u v),
      (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 = -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v))) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (w : K) (hw0 : w ≠ 0) (d : ℕ),
      Gz w 1 * ∑ j ∈ Finset.range (d / 2), tent w (d - 1 - 2 * j) = ∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * Gz w (i : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (w : K) (n : ℕ),
      xCoeff w n = ∑ f ∈ n.divisors, (f : K) * Fz w (f : ℤ)) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u v : K} [CharZero K] (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0)
    (hv1 : v ≠ 1) (huvm : u * v ≠ 1) (huvd : u * v⁻¹ ≠ 1) {M : ℕ} (hM : 0 < M),
      svComplex u v M = (∑ e ∈ M.divisors, 2 * (e : K) * (∑ i ∈ Finset.range e, ((Gz u 1 * ∑ j ∈ Finset.range ((i + 1) / 2), tent u (i - 2 * j)) * (Gz v 1 * ∑ j ∈ Finset.range ((e - i) / 2), tent v (e - i - 1 - 2 * j)) - (Gz u 1 * ∑ j ∈ Finset.range ((e - 1 - i) / 2), tent u (e - 1 - i - 1 - 2 * j)) * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j))))) - (∑ d ∈ M.divisors, 2 * (d : K) * ((Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j)) * (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j)))) + (∑ d ∈ M.divisors, (d : K) * (Gz v (d : ℤ) * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (Gz u 1 * ∑ j ∈ Finset.range (i / 2), tent u (i - 1 - 2 * j))) + Gz u (d : ℤ) * (∑ i ∈ Finset.Ico 1 d, ((d : K) - (i : K)) * (Gz v 1 * ∑ j ∈ Finset.range (i / 2), tent v (i - 1 - 2 * j))))) + (∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * (2 * ∑ f ∈ (M - a).divisors, (f : K) * (tent u f + tent v f))) - ∑ a ∈ Finset.Ico 1 M, ∑ d ∈ a.divisors, 2 * (d : K) * ((Gz u 1 * ∑ j ∈ Finset.range (d / 2), tent u (d - 1 - 2 * j)) * (Gz v (d : ℤ) * xCoeff v (M - a)) + (Gz v 1 * ∑ j ∈ Finset.range (d / 2), tent v (d - 1 - 2 * j)) * (Gz u (d : ℤ) * xCoeff u (M - a)))) ∧

    (∀ (d : ℕ) {r : ℝ} (h0 : 0 < r) (h1 : r < 1),
      Summable fun k : ℕ => ((k : ℝ) + 1) ^ d * r ^ k) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {B : ℝ} {d : ℕ} (hB : 0 ≤ B)
    {s : ℕ → ℕ → Finset ℤ} {a : ℕ → ℕ → ℤ → K}
    (ha : ∀ M k j, ‖a M k j‖ ≤ B * ((M : ℝ) + 1) ^ d)
    (hmaster : ∀ n : ℕ, ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ →
      ∑ k ∈ Finset.Icc 1 M,
          spectatorRows s a (unitSpectator q n) M k * (w ^ k + w⁻¹ ^ k - 2)
        = specAlpha (spectatorRows s a (unitSpectator q n)) w M
          + specTail (spectatorRows s a (unitSpectator q n)) w M
          + specGamma (spectatorRows s a (unitSpectator q n)) M),
      ∀ M k : ℕ, 1 ≤ k → k ≤ M → ∀ v : K, v ≠ 0 → ∑ j ∈ s M k, a M k j * v ^ j = 0) ∧

    (∀ {K : Type u_1} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {B : ℝ} {d : ℕ} (hB : 0 ≤ B) (c : ℕ → ℕ → K)
    (hc : ∀ N k, ‖c N k‖ ≤ B * ((N : ℝ) + 1) ^ d) {g : K → K → K}
    (hinv : ∀ q w : K, q ≠ 0 → 1 < ‖w‖ → ‖q‖ * ‖w‖ < 1 → g q (q * w) = g q w)
    (hrepr : ∀ q w : K, q ≠ 0 → ‖q‖ < ‖w‖ → ‖q‖ * ‖w‖ < 1 → ‖w‖ ≠ 1 →
      HasSum (fun M : ℕ =>
        (∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2)) * q ^ M) (g q w)),
      ∀ M : ℕ, ∀ w : K, 1 < ‖w‖ → ∑ k ∈ Finset.Icc 1 M, c M k * (w ^ k + w⁻¹ ^ k - 2) = specAlpha c w M + specTail c w M + specGamma c M) := by sorry
