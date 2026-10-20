-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_holevo_mean_distance
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.holevo_mean_distance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:21:11.948989+00:00
-- url     : https://prove2.me/theorems/22ec3d6d-5c22-4a0c-8976-4e9c54da2e78
-- title:
--   Lemma 9: Holevo and average trace norm
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   Let $p_k$ be a probability law and $\rho_k$ density matrices on a finite Hilbert space $H$; put $\bar\rho=\sum_kp_k\rho_k$, $D=\sum_kp_k\|\rho_k-\bar\rho\|_1$, and $\chi=S(\bar\rho)-\sum_kp_k S(\rho_k)$ in bits. For every $\epsilon\ge0$,
--
--   $$\chi\le\epsilon\quad\Longrightarrow\quad D\le\sqrt{2\epsilon}.$$
--
--   For $0\le\epsilon\le1$, the converse estimate is
--
--   $$D\le\epsilon\quad\Longrightarrow\quad \chi\le3\epsilon\log_2|H|+\max\{h_2(\epsilon),2\epsilon\}.$$
--
--   Only the second implication uses the binary entropy probability domain. Both statements allow zero ensemble weights and singular density matrices.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 36, Lemma 9: Holevo and average trace norm

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

/-- PDF pp.36–37, Lemma 9: sqrt(2 epsilon), entropy in bits, and quantum dimension.
The first implication allows every epsilon >= 0. Only the second implication, which
contains binary entropy, restricts epsilon to its probability domain [0,1]. -/
theorem holevo_mean_distance {L H : Type*} [Fintype L] [Fintype H]
    [Nonempty L] [Nonempty H] (p : L → ℝ) (rho : L → Op H) (hensemble : IsEnsemble p rho)
    (eps : ℝ) (hpos : 0 ≤ eps) :
    (ensembleHolevoBits p rho ≤ eps → meanDistance p rho ≤ Real.sqrt (2*eps)) ∧
    (eps ≤ 1 → meanDistance p rho ≤ eps → ensembleHolevoBits p rho ≤
      3*eps*logBits (Fintype.card H) + max (binEntropy2 eps) (2*eps)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
