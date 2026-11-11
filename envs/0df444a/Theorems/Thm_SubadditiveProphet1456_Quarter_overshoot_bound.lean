-- Prove2me | Theorems.Thm_SubadditiveProphet1456_Quarter_overshoot_bound
-- name    : SubadditiveProphet1456.Quarter.overshoot_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:06.46454+00:00
-- url     : https://prove2.me/theorems/a3d237ae-dccd-4ef0-b425-9ca460397b84
-- title:
--   Lemma A.2 — Overshoot bound with the prefix products
-- statement:
--   Fix the Appendix A standing setup: $0<\theta<1$, feasible $x$, an integer cap $N\ge1$, and any capped RSG family satisfying (16). For buyer $i$, item $j$, and $1\le h<N$, write $q_{ij}(h)=\Pr[b_{ij}\ge h]$, $\pi_{ij}=\Pr[j\in X_i]$, $\alpha_{ij}(h)=\prod_{k<i}(1-q_{kj}(h))$, $\rho_{ij}=\prod_{k<i}(1-\pi_{kj})$, $s_j=\prod_k(1-q_{kj}(h))$, and $f_{ij}(h)=\alpha_{ij}(h)-s_j$. Then
--   $$
--   \alpha_{ij}(h)q_{ij}(h+1)\le\pi_{ij}\bigl[(1+s_j^2)(1-s_j)-(s_j^2+s_j\rho_{ij}^2)f_{ij}(h)\bigr].
--   $$
--   Empty prefix products equal one, and $s_j$ depends on $h$. This is the complete overshoot bound (46) used to estimate the decay of the first-large-score process.
--
--   Differences from the source:
--   - encoding: Finite items and nonempty finite buyer type supports in fixed arrival order → Zero-based Fin indices and type supports Fin (k+1), with positive type probabilities; reason: Relabeling covers every source instance, including empty item or buyer sets; zero-probability labels are omitted from support
-- source:
--   Twan Kroll, Calum MacRury, Rebecca Reiffenhäuser, Siddharth M. Sundaram, STOC 2027 submission #1456 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1456.pdf, printed p.32, PDF p.33, Lemma A.2.

import Definitions.Def_SubadditiveProphet1456_Quarter_CapHeight
import Definitions.Def_SubadditiveProphet1456_Quarter_Machine

open scoped BigOperators NNReal ENNReal
open MeasureTheory

namespace SubadditiveProphet1456.Quarter

theorem overshoot_bound
    (n m : ℕ) (I : Instance n m) (θ : ℝ) (x : Fractional I)
    (N : ℕ) (φ : RSG I)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hx : Feasible I θ x) (hN : 1 ≤ N)
    (hφ : DistributionalEquation I x N φ)
    (i : Fin n) (j : Fin m) (h : ℕ) (hh : 1 ≤ h) (hhN : h < N) :
    α I φ i j h * q I φ i j (h+1) ≤
      π I x i j * ((1+(s I φ j h)^2)*(1-s I φ j h) -
        ((s I φ j h)^2 + s I φ j h*(ρ I x i j)^2)*f I φ i j h) := by sorry

end SubadditiveProphet1456.Quarter
