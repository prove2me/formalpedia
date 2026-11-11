-- Prove2me | Theorems.Thm_SpanForestStream_Unrestricted_lemma_4_4
-- name    : SpanForestStream.Unrestricted.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:32:02.483567+00:00
-- url     : https://prove2.me/theorems/0d54ea19-145c-4abc-9934-0a7bdc283bc8
-- title:
--   Lemma 4.4 — two elementary success-conditioning bounds (4.15)–(4.17)
-- statement:
--   Let $\pi$ be any joint law and $W$ any event with probability $p=\pi(W)>0$; $W$ may depend on private decoder coins. Then:
--   $$D_{\mathrm{KL}}\big(\pi[V\mid W]\,\big\|\,\pi[V]\big)\le\log_2(1/p)\quad\text{for every variable }V;\qquad(4.15)$$
--   if $A$ and $B$ are conditionally independent given $C$ under $\pi$, then
--   $$I_\pi(A;B\mid C,W)\le\log_2(1/p);\qquad(4.16)$$
--   and for arbitrary $A,M$,
--   $$p\,I_\pi(A;M\mid W)\le I_\pi(A;M)+H_\pi(\mathbf 1_W)\le I_\pi(A;M)+1.\qquad(4.17)$$
--   Here $I_\pi(A;B\mid C,W)$ is conditional mutual information under the success-conditioned law $\pi(\cdot\mid W)$, averaged over $C$ under that same law, and $I_\pi(A;M\mid W)$ is mutual information under $\pi(\cdot\mid W)$.
--
--   These bounds let the lower-bound arguments condition on success while charging information under the original law.
--
--   Differences from the source:
--   - encoding: any joint law and any collection of variables → a discrete law π on an arbitrary type Ω and variables as functions out of Ω (a collection of variables is one tuple-valued function); reason: the paper's laws are discrete; information in bits
--   - encoding: H_π(1_W) → the entropy of the Boolean variable [ω ∈ W] under π; reason: the binary indicator of W
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 29 (PDF 32), Lemma 4.4

import Mathlib
import Definitions.Def_SpanForestStream_Unrestricted_Info

open scoped ENNReal

namespace SpanForestStream.Unrestricted

open Classical in
/-- Lemma 4.4: for a joint law `π` and an event `W` of probability `p > 0`,
(4.15) `D_KL(π[V | W] ‖ π[V]) ≤ log₂(1/p)` for every variable `V`;
(4.16) if `A ⊥ B | C` under `π` then `I_π(A; B | C, W) ≤ log₂(1/p)`;
(4.17) `p I_π(A; M | W) ≤ I_π(A; M) + H_π(1_W) ≤ I_π(A; M) + 1`. -/
theorem lemma_4_4 {Ω : Type} (π : PMF Ω) (W : Set Ω) (hp : 0 < probOf π W) :
    (∀ {γ : Type} (V : Ω → γ),
      klBits ((condOn π W).map V) (π.map V) ≤
        ENNReal.ofReal (Real.logb 2 (1 / (probOf π W).toReal))) ∧
    (∀ {α β γ : Type} (A : Ω → α) (B : Ω → β) (C : Ω → γ), CondIndep π A B C →
      condMutualInfo (condOn π W) A B C ≤
        ENNReal.ofReal (Real.logb 2 (1 / (probOf π W).toReal))) ∧
    (∀ {α μ : Type} (A : Ω → α) (M : Ω → μ),
      probOf π W * mutualInfo (condOn π W) A M ≤
          mutualInfo π A M + entropyBits (π.map fun ω => decide (ω ∈ W)) ∧
        mutualInfo π A M + entropyBits (π.map fun ω => decide (ω ∈ W)) ≤
          mutualInfo π A M + 1) := by sorry

end SpanForestStream.Unrestricted
