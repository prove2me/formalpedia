-- Prove2me | Theorems.Thm_PostQual_Incumbent_theorem_2
-- name    : PostQual.Incumbent.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:30.537922+00:00
-- url     : https://prove2.me/theorems/74986071-19d6-486b-8a23-f5ace6d66147
-- title:
--   Theorem 2, p. 18 (PDF 19) — the incumbent's optimal drop-out price is b⋆_m(x0) ∧ p if m > m⋆(x0) and p ≤ p⋆_m(x0), else p
-- statement:
--   Throughout, $(\underline R,\overline R,N,\beta,K,f_e)$ satisfies the standing assumptions of §2 ($\underline R<\overline R$, $N\ge 2$, $\beta\in(0,1)$, $K>0$, $\Delta=K/\beta<\overline R-\underline R$, $f_e$ a density supported on $[\underline R,\overline R]$, positive and continuous there) and Assumption 1 ($F_e/f_e$ nondecreasing and convex on $[\underline R,\overline R]$). Write $\ell(x_0)=\max\{\underline R+\Delta,x_0\}$ for the left end of the incumbent's feasible drop-out prices.
--
--   For $x_0\in[\underline R,\overline R]$ let $m^\star(x_0)$, $b^\star_m(x_0)$, $p^\star_m(x_0)$ and $s^\star_m(x_0;p)$ be as in the model file. Then, for $1\le m\le m'\le N$:
--
--   **(i)**
--   1. $m^\star(x_0)$ is well defined: the ratio $\frac{(1-\beta)F_e(b-\Delta)}{\beta(b-x_0)f_e(b-\Delta)}$ is positive for $b\in(\max\{x_0,\underline R+\Delta\},\overline R+\Delta]$;
--   2. if $m>m^\star(x_0)$: the set defining $b^\star_m(x_0)$ is nonempty when $x_0>\underline R+\Delta$, the minimum defining $p^\star_m(x_0)$ is attained, and
--   $$p^\star_m(x_0)>b^\star_m(x_0)\ge x_0,\qquad b^\star_m(x_0)>x_0\ \text{ when } x_0\ne\underline R+\Delta;$$
--   3. $m^\star$ is nondecreasing in $x_0$; $b^\star_m(x_0)$ is nondecreasing in $x_0$ and nonincreasing in $m$; $p^\star_m(x_0)$ is nonincreasing in $x_0$ and nondecreasing in $m$ (wherever $m>m^\star$).
--
--   **(ii)** For every $p\ge\ell(x_0)$, the drop-out price
--   $$s^\star_m(x_0;p)=\begin{cases}b^\star_m(x_0)\wedge p,& m>m^\star(x_0),\ p\le p^\star_m(x_0),\\ p,&\text{otherwise},\end{cases}$$
--   lies in $[\ell(x_0),p]$, maximizes $b\mapsto\Pi^m_0(b;x_0,p)$ there, and $V^m_0(x_0,p)=\Pi^m_0(s^\star_m(x_0;p);x_0,p)$; moreover $s^\star_m(x_0;p)$ is nondecreasing in $x_0$ and in $p$ and nonincreasing in $m$.
--
--   The incumbent therefore either *competes*, staying in until the price falls to $b^\star_m(x_0)$, or *folds*, dropping out at once; which one depends on the number of remaining entrants and on whether the price is above the switching curve $p^\star_m(x_0)$.
--
--   **Formalization Note** The standing assumptions and Assumption 1 are the hypotheses `hS : P.Standing` and `hA1 : P.Assumption1`; positivity and continuity of $f_e$ on the support are an addition to the page, needed by its own formulas $H(b)=F_e(b-\Delta)/f_e(b-\Delta)$ and $\partial\Pi/\partial b$. The page's hypothesis that entrants follow Lemma 2 and Theorem 1 is how it derives (8)–(10); the statement is about the Bellman system (8)–(10) itself, and the game-theoretic layer is not modelled. "The optimal drop-out price is $s^\star$" is read as "$s^\star$ is a maximizer in (8)": at $p=p^\star_m(x_0)$ both $b^\star_m(x_0)$ and $p$ are maximizers (Lemma EC.1 (d)), so uniqueness would be false. $m^\star$'s minimum is read as an infimum over the half-open interval (the ratio has a zero denominator at $b=x_0$). "Nondecreasing"/"nonincreasing" are weak; monotonicity of $b^\star$, $p^\star$ is asserted only where the page defines them ($m>m^\star$).
-- source:
--   Zhang, Chen & Katok, “Now or Later?” When to deploy qualification screening in open-bid auction for re-sourcing, accepted manuscript (Operations Research 69(6), 2021; LBS Research Online eprint 1542), p. 18 (PDF 19), Theorem 2

import Mathlib
import Definitions.Def_PostQual_Incumbent_Model

namespace PostQual.Incumbent

/-- Theorem 2, p. 18: well-definedness, ordering and monotonicity of `m⋆`, `b⋆_m`, `p⋆_m` (part (i)),
and the optimality and monotonicity of the drop-out price `s⋆_m(x0; p)` in (8) (part (ii)). -/
theorem theorem_2 (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) :
    -- (i) m⋆ is well-defined: the minimized ratio is positive
    (∀ x0 ∈ Set.Icc P.Rlo P.Rhi, ∀ b ∈ Set.Ioc (max x0 (P.Rlo + P.Δ)) (P.Rhi + P.Δ),
      0 < P.ratio x0 b) ∧
    -- (i) b⋆, p⋆ are well-defined and ordered
    (∀ x0 ∈ Set.Icc P.Rlo P.Rhi, ∀ m : ℕ, 1 ≤ m → m ≤ P.N → P.mStar x0 < m →
      (P.Rlo + P.Δ < x0 →
        {b | b ∈ Set.Ioc x0 (P.Rhi + P.Δ) ∧ P.H b - P.L m b x0 < 0}.Nonempty) ∧
      IsLeast {b | P.bStar m x0 < b ∧
          0 ≤ P.Pi m b x0 (P.Rhi + P.Δ) - P.Pi m (P.bStar m x0) x0 (P.Rhi + P.Δ)}
        (P.pStar m x0) ∧
      x0 ≤ P.bStar m x0 ∧ P.bStar m x0 < P.pStar m x0 ∧
      (x0 ≠ P.Rlo + P.Δ → x0 < P.bStar m x0)) ∧
    -- (i) monotonicity
    MonotoneOn P.mStar (Set.Icc P.Rlo P.Rhi) ∧
    (∀ m : ℕ, 1 ≤ m → m ≤ P.N → ∀ x0 ∈ Set.Icc P.Rlo P.Rhi, ∀ x0' ∈ Set.Icc P.Rlo P.Rhi,
      x0 ≤ x0' → P.mStar x0' < m →
        P.bStar m x0 ≤ P.bStar m x0' ∧ P.pStar m x0' ≤ P.pStar m x0) ∧
    (∀ x0 ∈ Set.Icc P.Rlo P.Rhi, ∀ m m' : ℕ, 1 ≤ m → m ≤ m' → m' ≤ P.N → P.mStar x0 < m →
      P.bStar m' x0 ≤ P.bStar m x0 ∧ P.pStar m x0 ≤ P.pStar m' x0) ∧
    -- (ii) s⋆ is a maximizer in (8)
    (∀ x0 ∈ Set.Icc P.Rlo P.Rhi, ∀ m : ℕ, 1 ≤ m → m ≤ P.N → ∀ p, P.lo x0 ≤ p →
      P.sStar m x0 p ∈ Set.Icc (P.lo x0) p ∧
      (∀ b ∈ Set.Icc (P.lo x0) p, P.Pi m b x0 p ≤ P.Pi m (P.sStar m x0 p) x0 p) ∧
      P.V m x0 p = P.Pi m (P.sStar m x0 p) x0 p) ∧
    -- (ii) monotonicity of s⋆ in x0, p and m
    (∀ m : ℕ, 1 ≤ m → m ≤ P.N → ∀ x0 ∈ Set.Icc P.Rlo P.Rhi, ∀ x0' ∈ Set.Icc P.Rlo P.Rhi,
      x0 ≤ x0' → ∀ p, P.lo x0' ≤ p → P.sStar m x0 p ≤ P.sStar m x0' p) ∧
    (∀ m : ℕ, 1 ≤ m → m ≤ P.N → ∀ x0 ∈ Set.Icc P.Rlo P.Rhi, ∀ p p' : ℝ,
      P.lo x0 ≤ p → p ≤ p' → P.sStar m x0 p ≤ P.sStar m x0 p') ∧
    (∀ x0 ∈ Set.Icc P.Rlo P.Rhi, ∀ m m' : ℕ, 1 ≤ m → m ≤ m' → m' ≤ P.N → ∀ p, P.lo x0 ≤ p →
      P.sStar m' x0 p ≤ P.sStar m x0 p) := by sorry

end PostQual.Incumbent
