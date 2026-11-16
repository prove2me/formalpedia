-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_lemma_4_8
-- name    : SingleSampleCombPI.XOS.Supplement.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:42:43.814672+00:00
-- url     : https://prove2.me/theorems/053c15f3-d624-4b73-a2bd-7e04ce6027b2
-- title:
--   Lemma 4.8 — Divisible configuration free-disposal objective is normalized, nonnegative, monotone and submodular
-- statement:
--   For buyers with valid supporting-price maps, a configuration consists of a buyer $i$ and an allocation $x\in[0,1]^m$. For a finite configuration set $I$, evaluate free disposal after treating every configuration as a separate provisional entry:
--   $$f(I)=\mathrm{FD}(\{(i,x):(i,x)\in I\}).$$
--   Then $f(\varnothing)=0$, $f\ge0$, $f$ is monotone, and for all $I\subseteq J$ and $e\notin J$,
--   $$f(I\cup\{e\})-f(I)\ge f(J\cup\{e\})-f(J).$$
--   Several configurations of one buyer may belong to $I$. Restricting to the paper’s finite sets $O_i$ gives precisely its submodular objective; there is no finite-grid restriction on allocations.
--
--   Differences from the source:
--   - generalization: the finite configuration ground set constructed from Algorithm 5’s possible choices and an optimal allocation for continuous capped-XOS buyers → all finite sets of cube configurations for arbitrary buyers with valid one-sided supporting prices; reason: the source ground set is a special case; normalization, nonnegativity, monotonicity and diminishing returns hold on every finite configuration set without continuity or the origin of the configurations
--   - encoding: valuations and one-sided supporting-price maps on the source allocation domains → published Buyer, Regime and cube interfaces with real-valued functions evaluated only on the allocation domain; reason: the stored demand field is unused in noncomputational continuous statements; no support, continuity or concavity condition is added to the source valuation class
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Lemma 4.8, printed p. 22 / PDF p. 24; proof printed 22 / PDF 24.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_Continuous

namespace SingleSampleCombPI.XOS.Supplement

/-- Lemma 4.8, printed p. 22 / PDF p. 24. The configuration objective on
all finite sets of cube configurations. Specializing to the finite sets O_i
constructed in §4.2.1 gives the source instance. Several configurations from
the same buyer are permitted: the assertion is not restricted to feasible sets. -/
theorem lemma_4_8 {n m : ℕ} (b : Fin n → Buyer m)
    (hb : ∀ i, (b i).Valid .divisible) :
    divisibleConfigObj b ∅ = 0 ∧
    (∀ I, 0 ≤ divisibleConfigObj b I) ∧
    (∀ I J, I ⊆ J → divisibleConfigObj b I ≤ divisibleConfigObj b J) ∧
    @SubsamplingSM.Offline.IsSubmodular (DivConfig n m)
      (Classical.decEq _) (divisibleConfigObj b) := by sorry

end SingleSampleCombPI.XOS.Supplement
