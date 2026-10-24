-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P40_fiveInFive_improvesHashing
-- name    : QAlgorithms.Papers.Independent.Support50.P40.fiveInFive_improvesHashing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:02:37.760289+00:00
-- url     : https://prove2.me/theorems/6385cb17-5cda-4720-bb8d-d8931b078278
-- title:
--   Five-in-five cat concatenation strictly improves hashing
-- statement:
--   Consider independent qubit depolarization with identity-Pauli probability $f\in[0,1]$ and each other Pauli probability $g=(1-f)/3$. Let $C_{25}$ encode by the ordinary five-qubit cat encoder, followed on each output by the rotated five-qubit cat module $H^{\otimes5}V_{\rm cat}H$. Thus the rotated modules are adjacent to the physical channel. For a fixed complete coset frame of this code, let $q_{25}(f)$ denote its signed coset-entropy yield per physical channel use. Define $\tau(q)=\inf\{f\in[3/4,1]:q(f)>0\}$, and let $\tau_p$ be the corresponding ordinary length-$p$ cat threshold; $p=1$ is hashing.
--
--   This specified 25-qubit code and a compatible coset frame satisfy
--
--   $$
--   \tau(q_{25})<\tau_5<\tau_1,\qquad
--   q_{25}(f)>0\ \Longleftrightarrow\ f>\tau(q_{25})\quad(3/4\le f\le1).
--   $$
--
--   Whenever its yield is positive, it is an attainable limiting unassisted transmission rate using this fixed inner code and growing additive outer codes, with both entanglement fidelity and fidelity for every unknown normalized input tending to one. In particular, some fidelity in $[3/4,1]$ has positive $q_{25}$ although the hashing signed yield is nonpositive.
--
--   This is a constructive improvement within the specified concatenation family. The reported decimal $.80944$ is not an exact cutoff or a claim of optimal channel capacity.
-- source:
--   Quantum Channel Capacity of Very Noisy Channels, arXiv:quant-ph/9706061v3, PDF p. 19, Abstract and Section V.B: five-in-five concatenation improves the hashing threshold

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P40

namespace QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer

open scoped ComplexConjugate Matrix

noncomputable section

/-- PDF pp.1,19,24--25,31: the specified 25-qubit five-in-five construction
has a strictly lower positivity threshold than the five-cat and hashing,
and gives positive unassisted transmission where hashing's signed yield
is nonpositive. Printed decimals are approximate and are not exact cutoffs. -/
theorem fiveInFive_improvesHashing :
    ∃ C : InnerCode 24, ∃ T : CosetChoices C,
      innerEncoderMatrix C = fiveInFive ∧
      positivityThreshold (signedYield C T) < catThreshold 4 ∧
      catThreshold 4 < catThreshold 0 ∧
      (∀ f : ℝ, (3 / 4 : ℝ) ≤ f → f ≤ 1 →
        (0 < signedYield C T f ↔ positivityThreshold (signedYield C T) < f)) ∧
      (∀ f : ℝ, 0 ≤ f → f ≤ 1 → 0 < signedYield C T f →
        FixedInnerAchievable C f (signedYield C T f)) ∧
      ∃ f : ℝ, (3 / 4 : ℝ) ≤ f ∧ f ≤ 1 ∧ catYield 0 f ≤ 0 ∧
        0 < signedYield C T f := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P40
