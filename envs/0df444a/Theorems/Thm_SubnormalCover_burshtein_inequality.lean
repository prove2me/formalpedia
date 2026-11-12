-- Prove2me | Theorems.Thm_SubnormalCover_burshtein_inequality
-- name    : SubnormalCover.burshtein_inequality
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-14T12:46:22.57311+00:00
-- url     : https://prove2.me/theorems/d8846da8-e863-4402-b7c4-e5068d875b0d
-- title:
--   Burshtein-type inequality for subnormal uniform covers
-- statement:
--   Let $a_1G_1,\dots,a_kG_k$ be a **nontrivial uniform cover** of a group $G$: every $x\in G$ lies in exactly $w$ of the cosets, and not all $G_i$ equal $G$. Assume each $G_i$ is subnormal in $G$ of finite index, put $n_i=[G:G_i]$, $N=[n_1,\dots,n_k]$, and let $p^{*}$ be the largest prime divisor of $N$. Then **Burshtein's inequality** holds in the sharp form used by Sun: there is a $j$ with $p^{*}\mid n_j$ and
--   $$p^{*}\;<\;\bigl|\{i : n_i=n_j\}\bigr|\cdot\prod_{p\mid N}\frac{p}{p-1},$$
--   which is Theorem 4.1's estimate $p_r^{\beta_r}\le\varepsilon_r M_r\prod_{t=1}^r p_t/(p_t-1)$ (eq. (4.5)) weakened by $\beta_r\ge1$ and $\varepsilon_r<1$.
--
--   *Formalization note.* The inequality is stated over $\mathbb{N}$ with denominators cleared, as $p^{*}\prod_{p\mid N}(p-1) < |\{i:n_i=n_j\}|\prod_{p\mid N}p$; every truncated subtraction $p-1$ is exact because $p\ge 2$ is prime, and the finite-index hypothesis guarantees $N=\texttt{coverLcm K}\ge 2$, so $p^{*}=\texttt{maxPrimeFac }N$ really is a prime divisor of $N$.
-- source:
--   Z.-W. Sun, On the Herzog-Schönheim conjecture for uniform covers of groups, J. Algebra 273 (2004) 153-175, https://doi.org/10.1016/S0021-8693(03)00526-X, Theorem 4.1, eq. (4.5) (subnormal case), in the weakened form displayed in the proofs of Corollary 4.2 and Theorem 4.3; cf. Remark 4.1, eq. (4.6)

import Mathlib
import Definitions.Def_SubnormalCover_uniformCover
import Definitions.Def_BFFPyramidal_arithmetic

namespace SubnormalCover

open BFFPyramidal

theorem burshtein_inequality {G : Type*} [Group G] {k : ℕ}
    (K : Fin k → Subgroup G) (a : Fin k → G) (w : ℕ) (hcov : IsUniformCover K a w)
    (hfin : ∀ i, (K i).FiniteIndex) (hsn : ∀ i, (K i).IsSubnormal) (hnt : ∃ i, K i ≠ ⊤) :
    ∃ j : Fin k, maxPrimeFac (coverLcm K) ∣ (K j).index ∧
      maxPrimeFac (coverLcm K) * ∏ p ∈ (coverLcm K).primeFactors, (p - 1)
        < indexMultiplicity K ((K j).index) * ∏ p ∈ (coverLcm K).primeFactors, p := by
  sorry

end SubnormalCover
