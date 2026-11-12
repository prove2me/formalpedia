-- Prove2me | Theorems.Thm_SubnormalCover_multiplicity_ge_minFac
-- name    : SubnormalCover.multiplicity_ge_minFac
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-14T12:47:09.34927+00:00
-- url     : https://prove2.me/theorems/c532c0b1-2dc3-42ef-96e7-8183e9ed36c3
-- title:
--   Multiplicity of a subnormal uniform cover is at least the least prime
-- statement:
--   **Main theorem (Sun, Theorem 4.3(i)).** Let $a_1G_1,\dots,a_kG_k$ be a nontrivial uniform cover of an arbitrary group $G$ (each $x\in G$ lies in exactly $w$ of the cosets, and some $G_i\ne G$) by subnormal subgroups of finite index. Put $n_i=[G:G_i]$ and $N=[n_1,\dots,n_k]$, and let $p_*$ and $p^{*}$ be the smallest and largest prime divisors of $N$. Then among the $k$ indices there is a multiple of $p^{*}$ occurring at least $p_*$ times: there exists $j$ with $p^{*}\mid n_j$ and $|\{i : n_i=n_j\}|\ge p_*$. In particular the maximal multiplicity $M=\max_j|\{i:n_i=n_j\}|$ satisfies $M\ge p_*$, which is the quantitative form of Theorem 1.1 and answers Erd\H{o}s' open question negatively for subnormal covers.
--
--   *Formalization note.* $N$ is `coverLcm K` (the lcm of the indices), $p^{*}$ is `BFFPyramidal.maxPrimeFac N` and $p_*$ is `Nat.minFac N`; the hypotheses `hcov` and `hnt` already force $k\ge 2$ and $N\ge 2$, so $p_*$ is a genuine prime (not the junk value $\texttt{minFac }1=1$) and no separate $1<k$ assumption is needed.
-- source:
--   Z.-W. Sun, On the Herzog-Schönheim conjecture for uniform covers of groups, J. Algebra 273 (2004) 153-175, https://doi.org/10.1016/S0021-8693(03)00526-X, Theorem 4.3(i), first half ($M \ge p_*$); equivalently the non-asymptotic half of Theorem 1.1

import Mathlib
import Definitions.Def_SubnormalCover_uniformCover
import Definitions.Def_BFFPyramidal_arithmetic

namespace SubnormalCover

open BFFPyramidal

theorem multiplicity_ge_minFac {G : Type*} [Group G] {k : ℕ}
    (K : Fin k → Subgroup G) (a : Fin k → G) (w : ℕ) (hcov : IsUniformCover K a w)
    (hfin : ∀ i, (K i).FiniteIndex) (hsn : ∀ i, (K i).IsSubnormal) (hnt : ∃ i, K i ≠ ⊤) :
    ∃ j : Fin k, maxPrimeFac (coverLcm K) ∣ (K j).index ∧
      Nat.minFac (coverLcm K) ≤ indexMultiplicity K ((K j).index) := by
  sorry

end SubnormalCover
