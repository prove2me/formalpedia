-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_noisy_local_box
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.noisy_local_box
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:00:04.856622+00:00
-- url     : https://prove2.me/theorems/d829f771-5bd0-4bee-bea6-5833bb1e4d9f
-- title:
--   Noisy local-component boxes cannot be distilled exactly
-- statement:
--   In the binary two-party Bell scenario, let $B_{\rm PR}$ have probabilities $P(a,b\mid x,y)=1/2$ when $a\oplus b=xy$, and zero otherwise. Let $B_{\rm free}$ be any local shared-randomness box, and set $B=(1-\epsilon)B_{\rm PR}+\epsilon B_{\rm free}$ with $0<\epsilon\le1$. Allowed channels are classical no-signalling boxes and free channels are local boxes; transformations are the maximal physical deterministic superchannels preserving these two families. For every positive finite integer $n$,
--   $$R_{\min,\mathcal O}(B^{\otimes n})=1,\qquad B^{\otimes n}\not\longrightarrow B_{\rm PR}\ \text{exactly by a free superchannel}.$$
--   The copy registers are grouped by party and permit arbitrary collective local responses. No full-rank assumption on $B_{\rm free}$ is needed.
--
--   The paper recovers this exact no-distillation result from Refs.[103,107]; it states no numerical approximate-error bound here.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 4, Noisy local-component boxes cannot be distilled exactly

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- Noisy local-component boxes, PDF p.4: min-resource one for every positive
finite copy number, and no exact free conversion to PR. Full-rank local noise
is unnecessary. The result is recovered from source Refs.[103,107]. -/
theorem noisy_local_box (P : Kernel binarySplit) (hP : NoSignalling binarySplit P)
    (hlocal : IsLocalBox binarySplit P) (e : ℝ) (he : 0 < e) (he1 : e ≤ 1)
    (n : ℕ) (hn : 0 < n) :
    let B := boxChoi (copySplit n) (tensorKernel n (noisyKernel P e))
    minimum boxTheory B = 1 ∧
    ¬ Converts boxTheory B (boxChoi binarySplit prKernel) 0 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
