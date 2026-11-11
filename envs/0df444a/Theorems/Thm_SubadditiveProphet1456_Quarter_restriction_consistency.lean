-- Prove2me | Theorems.Thm_SubadditiveProphet1456_Quarter_restriction_consistency
-- name    : SubadditiveProphet1456.Quarter.restriction_consistency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:55.870356+00:00
-- url     : https://prove2.me/theorems/4211d09f-df7a-44e9-acd4-286dcb91fcd0
-- title:
--   Claim 4.5 — Restriction consistency at every depth
-- statement:
--   For independent bundle laws $\mu_i$, any buyer $i$, depth $h\ge0$, and bundles $B\subseteq A$,
--   $$
--   \operatorname{CapHeight}(i,h,B)\ \overset d=\ \operatorname{CapHeight}(i,h,A)|_B.
--   $$
--   Restriction sets coordinates outside $B$ to zero. The conclusion compares joint score-vector laws, preserving the dependence among coordinates. This is the restriction interface used in the constructive distributional guarantee.
--
--   Differences from the source:
--   - encoding: Finite items and nonempty finite buyer type supports in fixed arrival order → Zero-based Fin indices and type supports Fin (k+1), with positive type probabilities; reason: Relabeling covers every source instance, including empty item or buyer sets; zero-probability labels are omitted from support
--   - generalization: CapHeight consistency for the tentative distributions of the standing LP setup → CapHeight consistency for arbitrary independent bundle PMFs; reason: The consistency arguments use no LP constraints; taking the induced tentative laws recovers the source
-- source:
--   Twan Kroll, Calum MacRury, Rebecca Reiffenhäuser, Siddharth M. Sundaram, STOC 2027 submission #1456 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1456.pdf, printed p.16, PDF p.17, Claim 4.5.

import Definitions.Def_SubadditiveProphet1456_Quarter_CapHeight
import Definitions.Def_SubadditiveProphet1456_Quarter_Machine

open scoped BigOperators NNReal ENNReal
open MeasureTheory

namespace SubadditiveProphet1456.Quarter

theorem restriction_consistency
    (n m : ℕ) (μ : Fin n → PMF (Bundle m)) (i : Fin n)
    (h : ℕ) (B A : Bundle m) (hBA : B ⊆ A) :
    capHeight μ i h B = (capHeight μ i h A).map (restrictScore B) := by sorry

end SubadditiveProphet1456.Quarter
