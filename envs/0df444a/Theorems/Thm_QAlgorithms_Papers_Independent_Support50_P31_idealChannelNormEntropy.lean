-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P31_idealChannelNormEntropy
-- name    : QAlgorithms.Papers.Independent.Support50.P31.idealChannelNormEntropy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:26:49.962006+00:00
-- url     : https://prove2.me/theorems/ea589fbc-904e-433e-afe3-1b18eb3fc0fc
-- title:
--   An ideal ancilla preserves maximal norms and minimum entropy
-- statement:
--   Let $\Phi$ be a completely positive trace-preserving endomorphism on a nonzero finite-dimensional complex Hilbert space, and let $\operatorname{Id}_A$ be the identity channel on another such space. Write $\nu_p$ for maximum output Schatten $p$-norm (operator norm at infinity), and $\nu_H$ for minimum output entropy in natural units, optimizing over all joint density inputs. Then
--   $$
--   \nu_p(\operatorname{Id}_A\otimes\Phi)=\nu_p(\Phi)
--   \quad(1\le p\le\infty),\qquad
--   \nu_H(\operatorname{Id}_A\otimes\Phi)=\nu_H(\Phi).
--   $$
--   The ideal register cannot improve these objectives even when its input is entangled with the channel input. The source's separate minus-infinity branch is false and is explicitly deferred.
-- source:
--   On some additivity problems in quantum information theory, arXiv:math-ph/0003002v2, PDF p. 5, §3, Lemma (9), p and H branches

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P31

noncomputable section

open Filter Asymptotics

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P31

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten)

open QAlgorithms.Papers.Independent.Gap48.P03 (holevoQuantity)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

open QAlgorithms.Papers.Independent.Dependency50.P44 (tensorChannels)

/-- PDF p.5, Lemma (9), valid norm and entropy branches only. The ideal register
is first, a coordinate permutation of Phi tensor Id. False minus-infinity
branch is separately deferred, rather than silently included. -/
theorem idealChannelNormEntropy {I J : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J] (Phi : Superop I I) (hPhi : IsChannel Phi) :
    (∀ p : ℝ≥0∞, 1 ≤ p → nuP p (idTensorSuperop (R := J) Phi) = nuP p Phi) ∧
      nuH (idTensorSuperop (R := J) Phi) = nuH Phi := by sorry

end QAlgorithms.Papers.Independent.Support50.P31

end
