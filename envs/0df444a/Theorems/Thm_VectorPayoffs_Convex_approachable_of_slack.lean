-- Prove2me | Theorems.Thm_VectorPayoffs_Convex_approachable_of_slack
-- name    : VectorPayoffs.Convex.approachable_of_slack
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:23:18.209296+00:00
-- url     : https://prove2.me/theorems/bb54c248-9b4b-457f-b837-292e023abfe3
-- title:
--   Blackwell's Theorem 1 with approximate separation $\kappa/n$
-- statement:
--   Work in the setting of Blackwell's repeated game with vector payoffs: $M=\|m(i,j)\|$ is an $r\times s$ matrix of probability distributions on a closed bounded convex set $X\subseteq\mathbb R^N$, with means $\bar m(i,j)$, and for a mixed action $p$ of player I
--   $$R(p)=\operatorname{conv}\Big\{\sum_{i}p_i\,\bar m(i,j):1\le j\le s\Big\}.$$
--   Let $S\subseteq\mathbb R^N$, let $\kappa\ge0$, and let $f=\{f_n\}$ be a strategy of player I. Write $\bar x_n=\frac1n(x_1+\dots+x_n)$ for the average of a history $(x_1,\dots,x_n)$. Suppose that for every $n\ge1$ and every history with $\bar x_n\in X\setminus S$ there is a point $y\in S$ closest to $\bar x_n$ such that
--   $$\langle \bar x_n-y,\;w-y\rangle\;\le\;\frac{\kappa}{n}\qquad\text{for all }w\in R\big(f_n(x_1,\dots,x_n)\big).$$
--   Then $S$ is approachable with $f$: for every $\varepsilon>0$ there is $N_0$ such that for every strategy of II and every play of the two strategies,
--   $$\mathrm{Prob}\{\operatorname{dist}(\bar x_n,S)\ge\varepsilon\ \text{for some } n\ge N_0\}<\varepsilon .$$
--
--   For $\kappa=0$ this is the sufficient condition of Blackwell's THEOREM 1 (where $f_n$ plays $p(\bar x_n)$ and the hyperplane through $y$ perpendicular to $\bar x_n y$ separates $\bar x_n$ from $R(p(\bar x_n))$). The proof of THEOREM 1 uses the hyperplane condition only through the cross term in the recursion for $\operatorname{dist}(\bar x_n,S)^2$, which is multiplied by a factor of order $1/n$, so an error of order $\kappa/n$ is absorbed in the constant of the recursion. The relaxed form is what one needs to build a *measurable* strategy from a finite net of mixed actions.
--
--   **Formalization Note** The condition is required only for averages lying in $X$ (outcomes lie in $X$ almost surely, hence so do the averages). "A closest point" is read as some closest point $y\in S$; the strategy $f$ is a measurable strategy in the sense of the definition file, and the quantification over plays is the one of `ApproachableWith`.
-- source:
--   D. Blackwell, An analog of the minimax theorem for vector payoffs, Pacific J. Math. 6(1) (1956), pp. 3-5, THEOREM 1 and its proof (variant: the separation inequality is relaxed to kappa/n)

import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game

open MeasureTheory

namespace VectorPayoffs.Convex

/-- Blackwell (1956), §2, THEOREM 1 with approximate separation: if the hyperplane condition of
THEOREM 1 holds up to an error `κ / n` at stage `n`, the set `S` is still approachable with `f`. -/
theorem approachable_of_slack {N r s : ℕ} (G : Game N r s) (S : Set (E N)) (κ : ℝ) (hκ : 0 ≤ κ)
    (f : Strategy N r)
    (hslack : ∀ n, 1 ≤ n → ∀ h : Fin n → E N, avgHist h ∈ G.X → avgHist h ∉ S →
      ∃ y ∈ S, (∀ z ∈ S, dist (avgHist h) y ≤ dist (avgHist h) z) ∧
        ∀ w ∈ G.R (f.toFun n h), inner ℝ (avgHist h - y) (w - y) ≤ κ / n) :
    G.ApproachableWith S f := by sorry

end VectorPayoffs.Convex
