-- Prove2me | Theorems.Thm_QuantumLTF_Membership_lemma_3_3
-- name    : QuantumLTF.Membership.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:35:52.142576+00:00
-- url     : https://prove2.me/theorems/4e47f15e-286b-4dc8-9449-fc1d34ff9822
-- title:
--   Lemma 3.3 — the Fourier transform on the centered grid
-- statement:
--   $\mathrm{QFT}_{G_b}$, defined by $|x\rangle\mapsto2^{-b/2}\sum_{u\in G_b}e^{2\pi i2^bxu}|u\rangle$, is the same as the usual quantum Fourier transform up to composition before and after with a tensor product of $b$ single-qubit unitaries: there are single-qubit unitaries $u_0,\dots,u_{b-1}$ with
--   $$\mathrm{QFT}_{G_b}=\Bigl(\bigotimes_iu_i\Bigr)\mathrm{QFT}_b\Bigl(\bigotimes_iu_i\Bigr).$$
--   Centering the grid therefore costs only linearly many single-qubit gates. This is [GAW19, Claim 19].
--
--   Differences from the source:
--   - generalization: a tensor product of b single-qubit unitaries before and after → the same tensor product on both sides; reason: Eq. (48) and the next line give this U; it specializes to the printed sentence
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Lemma 3.3, Eqs. (44)–(48), p. 27 (PDF p. 28)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QuantumLTF_Membership_tensorSingle

namespace QuantumLTF.Membership

open QAlgorithms

/-- **Lemma 3.3 ([GAW19, Claim 19]).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Lemma 3.3, p. 27 (PDF p. 28), Eqs. (44)–(48):
`QFT_{G_b}` is the same as the usual quantum Fourier transform up to composition before and after with
a tensor product of `b` single-qubit unitaries.

**Formalization Note.** `gridQFT b` is Eq. (44) and `qftQubits b` is Eq. (47), both with `|j⟩` read most
significant bit first. The same `U` stands on both sides (Eq. (48) and the line after it). -/
theorem lemma_3_3 (b : ℕ) :
    ∃ u : Fin b → Matrix Bool Bool ℂ, (∀ i, u i ∈ Matrix.unitaryGroup Bool ℂ) ∧
      gridQFT b = tensorSingle u * qftQubits b * tensorSingle u := by sorry

end QuantumLTF.Membership
