-- Prove2me | Theorems.Thm_ShockWear_Inherit_Supplement_theorem34
-- name    : ShockWear.Inherit.Supplement.theorem34
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T23:53:35.301195+00:00
-- url     : https://prove2.me/theorems/1fe85a96-3904-4abb-b003-bc1ba0dcc0a3
-- title:
--   Theorem 3.4 — SCₙ transfers (corrected: density coefficient index includes p₁)
-- statement:
--   Let $\lambda>0$ and $1=\bar P_0\ge\bar P_1\ge\cdots\ge0$, and let $h$ and $\bar H$ be (2.3) and (2.1). For every positive integer $n$ and either sign $\varepsilon\in\{-1,1\}$, both transfers hold:
--
--   $$
--   [p_{j+k+1}]_{j,k\ge0}\text{ is SC}_n(\varepsilon)
--   \Longrightarrow h(s+t)\text{ is SC}_n(\varepsilon)\text{ on }s,t>0,
--   $$
--   $$
--   [\bar P_{j+k}]_{j,k\ge0}\text{ is SC}_n(\varepsilon)
--   \Longrightarrow \bar H(s+t)\text{ is SC}_n(\varepsilon)\text{ on }s,t>0.
--   $$
--
--   These are two independent implications. Each antecedent concerns only minors of size $n$, not all smaller orders.
--
--   **Formalization Note** The source prints $p_{j+k}$ on $j,k\ge1$ in (3.15); we state the corrected coefficient kernel $p_{j+k+1}$ on $j,k\ge0$ (equivalently $p_{j+k-1}$ on $j,k\ge1$). The density expansion (2.3) starts at $p_1$, and its double exponential generating function has precisely these coefficients. For the printed version, $\lambda=1$, $p_1=1/100$, and $p_k=(99/200)(1/2)^{k-2}$ for $k\ge2$ give a rank-one printed Hankel kernel, hence SC₂ with positive sign, but $h(u)=.99e^{-u/2}-.98e^{-u}$ has $hh''-(h')^2=-(4851/20000)e^{-3u/2}<0$. The corrected hypothesis excludes that counterexample. The survival transfer (3.16) is unchanged.
--
--   Differences from the source:
--   - encoding: probabilities with P₀=1 and positive shock rate → explicit λ>0, P₀=1, antitonicity and nonnegativity; reason: these are (1.1)–(2.2) and the theorem preamble
--   - encoding: arbitrary positive order n, either sign, and ordered real/integer samples → Fin n matrices, StrictMono samples, explicit n≥1 and ε=±1; reason: exact ordered determinants on the full source domains
--   - correction: (3.15) assumes SCₙ of pⱼ₊ₖ for j,k≥1 → SCₙ of pⱼ₊ₖ₊₁ for j,k≥0; both transfer conclusions retained; reason: (2.3) and the double generating-function expansion control p₁; the p₁=1/100 geometric-tail counterexample in the Formalization Note refutes the printed index
--   - generalization: H is a proper life distribution, implicitly Pₖ→0 → the analytic class assertion also allows defective shock survivals; reason: bounded nonnegative coefficients still give convergent Poisson series and the same shape conclusion; every proper source law is included
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 635, Theorem 3.4; https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model
import Definitions.Def_ShockWear_Inherit_Supplement_TotalPositivity

namespace ShockWear.Inherit.Supplement

open MeasureTheory
open scoped ENNReal

theorem theorem34 (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 = 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (n : ℕ) (hn : 1 ≤ n) (eps : ℝ) (heps : eps = 1 ∨ eps = -1) :
    (IsSC n eps Set.univ Set.univ (fun j k : ℕ => failProb P (j + k + 1)) →
      IsSC n eps (Set.Ioi 0) (Set.Ioi 0) (fun s t : ℝ => shockDens lam P (s + t))) ∧
    (IsSC n eps Set.univ Set.univ (fun j k : ℕ => P (j + k)) →
      IsSC n eps (Set.Ioi 0) (Set.Ioi 0)
        (fun s t : ℝ => ShockWear.CumDamage.shockSurv lam P (s + t))) := by sorry

end ShockWear.Inherit.Supplement
