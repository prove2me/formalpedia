-- Prove2me | Theorems.Thm_SubadditiveProphet1456_Quarter_capping_consistency
-- name    : SubadditiveProphet1456.Quarter.capping_consistency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:55.952063+00:00
-- url     : https://prove2.me/theorems/a1275a6d-e785-4ba8-b8ea-7cce851f401f
-- title:
--   Claim 4.6 — Capping consistency for all larger depths
-- statement:
--   For independent bundle laws $\mu_i$, any buyer $i$, integers $\ell\ge h\ge0$, and any bundle $A$,
--   $$
--   \operatorname{CapHeight}(i,\ell,A)\wedge h\ \overset d=\ \operatorname{CapHeight}(i,h,A).
--   $$
--   The minimum with $h$ is coordinatewise and acts on the entire vector law. Depth zero and empty bundles are included. This is the capping interface needed to express a depth-$N$ score in terms of full depth-$N$ references.
--
--   Differences from the source:
--   - encoding: Finite items and nonempty finite buyer type supports in fixed arrival order → Zero-based Fin indices and type supports Fin (k+1), with positive type probabilities; reason: Relabeling covers every source instance, including empty item or buyer sets; zero-probability labels are omitted from support
--   - generalization: CapHeight consistency for the tentative distributions of the standing LP setup → CapHeight consistency for arbitrary independent bundle PMFs; reason: The consistency arguments use no LP constraints; taking the induced tentative laws recovers the source
-- source:
--   Twan Kroll, Calum MacRury, Rebecca Reiffenhäuser, Siddharth M. Sundaram, STOC 2027 submission #1456 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1456.pdf, printed p.16, PDF p.17, Claim 4.6.

import Definitions.Def_SubadditiveProphet1456_Quarter_CapHeight
import Definitions.Def_SubadditiveProphet1456_Quarter_Machine

open scoped BigOperators NNReal ENNReal
open MeasureTheory

namespace SubadditiveProphet1456.Quarter

theorem capping_consistency
    (n m : ℕ) (μ : Fin n → PMF (Bundle m)) (i : Fin n)
    (ℓ h : ℕ) (hℓ : h ≤ ℓ) (A : Bundle m) :
    (capHeight μ i ℓ A).map (capScore h) = capHeight μ i h A := by sorry

end SubadditiveProphet1456.Quarter
