-- Prove2me | Theorems.Thm_RobustDP_ChiSquare_lemma5_value_identity
-- name    : RobustDP.ChiSquare.lemma5_value_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:38:11.948119+00:00
-- url     : https://prove2.me/theorems/63fa1f77-c5e9-4f4d-a020-cc541e8191d9
-- title:
--   Lemma 5 — worst-case expectation over the χ² ball (46) equals $\max_{\mu\ge0}\{E^q[v-\mu]-\sqrt{t\,\mathrm{Var}^q[v-\mu]}\}$
-- statement:
--   Let $\mathcal S$ be a finite set of states, $q\in\mathcal M(\mathcal S)$ a probability measure with $q(s)>0$ for every $s$, $t\ge 0$ a radius, and $v:\mathcal S\to\mathbb R$ a value vector. Let
--
--   $$
--   \mathcal P=\Big\{p\in\mathcal M(\mathcal S):\ \sum_{s\in\mathcal S}\frac{(p(s)-q(s))^2}{q(s)}\le t\Big\}
--   $$
--
--   be the χ² set (46). Then the problem
--
--   $$
--   \text{minimize } \mathbf E^p[v]\quad\text{subject to } p\in\mathcal P \tag{47}
--   $$
--
--   has an optimal solution, and its optimal value equals
--
--   $$
--   \max_{\mu\ge 0}\Big\{\mathbf E^q[v-\mu]-\sqrt{t\,\mathbf{Var}^q[v-\mu]}\Big\}, \tag{48}
--   $$
--
--   where $\mu$ ranges over vectors $\mu:\mathcal S\to\mathbb R$ with $\mu(s)\ge 0$ for all $s$, and the maximum in (48) is attained.
--
--   In robust dynamic programming each robust Bellman update solves the inner problem $\inf_{p\in\mathcal P(s,a)}\mathbf E^p[v]$ for every state–action pair. Lemma 5 turns this problem over the χ² ball into a concave maximization over a nonnegative multiplier that, by (52)–(53), is a one-dimensional search. The nonnegativity constraint $p\ge 0$ is what makes $\mu$ appear: without it the value would be $\mathbf E^q[v]-\sqrt{t\,\mathbf{Var}^q[v]}$.
--
--   **Formalization Note** The statement asserts a single real number that is both the least element of $\{\mathbf E^p[v]:p\in\mathcal P\}$ and the greatest element of $\{g(\mu):\mu\ge 0\}$; the page writes "minimize" and "max". The positivity $q(s)>0$ is needed because the page divides by $q(s)$ (Lean's $x/0=0$ would silently drop such coordinates); in the paper $q$ is an empirical distribution and states with $q(s)=0$ are removed. The page puts no sign condition on $t$; $t\ge 0$ is assumed ($t<0$ makes $\mathcal P$ empty, and `Real.sqrt` of a negative number is $0$). The finiteness of $\mathcal S$ is the standing restriction of Section 4 (p. 15); nonemptiness follows from $\sum_s q(s)=1$. The lemma's second claim, "the complexity of (48) is $\mathcal O(|\mathcal S|\log(|\mathcal S|))$", is a statement about an algorithm and is not formalized.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 18, Lemma 5, eqs. (46)–(48)

import Mathlib
import Definitions.Def_RobustDP_ChiSquare_Moments
import Definitions.Def_RobustDP_ChiSquare_ChiSqSet

namespace RobustDP.ChiSquare

/-- Lemma 5 (Iyengar, TR-2002-07, p. 18), value identity: for a centre `q ∈ M(S)` with
`q(s) > 0` and a radius `t ≥ 0`, the minimum of `Eᵖ[v]` over the χ² set (46) exists and equals
the maximum over multipliers `μ ≥ 0` of `E^q[v − μ] − √(t Var^q[v − μ])` (problem (48)).
The complexity claim of the lemma is not formalized. -/
theorem lemma5_value_identity {S : Type*} [Fintype S] (q : S → ℝ)
    (hq : q ∈ stdSimplex ℝ S) (hq_pos : ∀ s, 0 < q s) (t : ℝ) (ht : 0 ≤ t) (v : S → ℝ) :
    ∃ val : ℝ,
      IsLeast ((fun p => expect p v) '' chiSqSet q t) val ∧
      IsGreatest ((fun μ => dualObj q t v μ) '' {μ : S → ℝ | 0 ≤ μ}) val := by sorry

end RobustDP.ChiSquare
